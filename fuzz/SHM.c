#include <sys/shm.h>
#include "alloc-inl.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>

static s32 shm_id;                    /* ID of the SHM region             */
u8* trace_bits;

static u8  virgin_bits[MAP_SIZE];     /* Regions yet untouched by fuzzing */

#define MAP_SIZE_POW2       16
#define MAP_SIZE            (1 << MAP_SIZE_POW2)

static void remove_shm(void) {

  shmctl(shm_id, IPC_RMID, NULL);

}


void setup_shm(void) {

  u8* shm_str;

  
  //  memset(virgin_tmout, 255, MAP_SIZE);
  //  memset(virgin_crash, 255, MAP_SIZE);

  shm_id = shmget(IPC_PRIVATE, MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);

  if (shm_id < 0) PFATAL("shmget() failed");

  atexit(remove_shm);

  shm_str = alloc_printf("%d", shm_id);

  /* If somebody is asking us to fuzz instrumented binaries in dumb mode,
     we don't want them to detect instrumentation, since we won't be sending
     fork server commands. This should be replaced with better auto-detection
     later on, perhaps? */

  setenv(SHM_ENV_VAR, shm_str, 1);

  ck_free(shm_str);

  trace_bits = shmat(shm_id, NULL, 0);
  
  if (!trace_bits) PFATAL("shmat() failed");

}

void setup_shm_aux(void) {

  // if (!in_bitmap)
  memset(virgin_bits, 255, MAP_SIZE);

//  printf("Init:\n");
//  for (u32 j = 0; j < MAP_SIZE; j++){
//    if (virgin_bits[j]) {
//      printf ("%d ", j);
//    }
//  }
//  printf("\n");

  
  u8* shm_str;

  shm_str = getenv(SHM_ENV_VAR);

  if (shm_str == NULL) PFATAL("getenv() failed");

  sscanf(shm_str, "%d", &shm_id);
  // shm_id = shmget(shm_str, MAP_SIZE, 0600);

  //ck_free(shm_str);

  trace_bits = shmat(shm_id, NULL, 0);
  
  if (!trace_bits) PFATAL("shmat() failed");

}


CAMLprim value setup_shm_prim(value unit)
{
  setup_shm();
  //printf ("SHM Setup succesful!\n");
  return Val_unit;
}

CAMLprim value setup_shm_prim_aux(value unit)
{
  printf ("Preparing to setup aux...\n");
  setup_shm_aux();
  printf ("SHM Setup (aux) succesful!\n");
  return Val_unit;
}


CAMLprim value copy_trace_bits( value ml_array )
{
  //  printf("Entering copy_trace_bits....\n");
    int i, len;
    len = Wosize_val(ml_array);
    printf("Size: %d\n", len);
    for (i=0; i < len; i++)
    {
      // *2 for some reason probably to do with ocaml encoding
      caml_modify(&Field(ml_array, i), Val_int (trace_bits[i]));
    }

    //    printf("Returning from copy trace bits...\n");
    return Val_unit ;
}

CAMLprim value reset_trace_bits(value unit)
{
  //  printf("Entering reset trace bits...\n");
  fflush(stdout);
  int i;
  //TODO: memset
  for (i=0; i<MAP_SIZE; i++){
    trace_bits[i] = 0;
  }
  //  printf("Returnging from reset trace bits...\n");
  return Val_unit ;
}

/* AFL-FUZZ borrowed functions to obtain faster statistics */


/* Count the number of bits set in the provided bitmap. Used for the status
   screen several times every second, does not have to be fast. */

static u32 count_bits(u8* mem) {

  u32* ptr = (u32*)mem;
  u32  i   = (MAP_SIZE >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This gets called on the inverse, virgin bitmap; optimize for sparse
       data. */

    if (v == 0xffffffff) {
      ret += 32;
      continue;
    }

    v -= ((v >> 1) & 0x55555555);
    v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
    ret += (((v + (v >> 4)) & 0xF0F0F0F) * 0x01010101) >> 24;

  }

  return ret;

}


#define FF(_b)  (0xff << ((_b) << 3))

/* Count the number of bytes set in the bitmap. Called fairly sporadically,
   mostly to update the status screen or calibrate and examine confirmed
   new paths. */

static u32 count_bytes(u8* mem) {

  u32* ptr = (u32*)mem;
  u32  i   = (MAP_SIZE >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    if (!v) continue;
    if (v & FF(0)) ret++;
    if (v & FF(1)) ret++;
    if (v & FF(2)) ret++;
    if (v & FF(3)) ret++;

  }

  //printf("Counted Bytes: %d\n", ret);
  return ret;

}

CAMLprim value count_bytes_aux(void){
  return Val_int(count_bytes(trace_bits));
}


/* Count the number of non-255 bytes set in the bitmap. Used strictly for the
   status screen, several calls per second or so. */

static u32 count_non_255_bytes(u8* mem) {

  u32* ptr = (u32*)mem;
  u32  i   = (MAP_SIZE >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This is called on the virgin bitmap, so optimize for the most likely
       case. */

    if (v == 0xffffffff) continue;
    if ((v & FF(0)) != FF(0)) ret++;
    if ((v & FF(1)) != FF(1)) ret++;
    if ((v & FF(2)) != FF(2)) ret++;
    if ((v & FF(3)) != FF(3)) ret++;

  }

  return ret;

}

CAMLprim value count_non_virgin_bytes(void){
  return Val_int(count_non_255_bytes(virgin_bits));
}



/* Check if the current execution path brings anything new to the table.
   Update virgin bits to reflect the finds. Returns 1 if the only change is
   the hit-count for a particular tuple; 2 if there are new tuples seen. 
   Updates the map, so subsequent calls will always return 0.

   This function is called after every exec() on a fairly large buffer, so
   it needs to be fast. We do this in 32-bit and 64-bit flavors. */

static inline u8 has_new_bits(u8* virgin_map) {

  //  count_bytes(trace_bits);
  //  count_non_255_bytes(virgin_bits);
  
#ifdef __x86_64__

  u64* current = (u64*)trace_bits;
  u64* virgin  = (u64*)virgin_map;

  u32  i = (MAP_SIZE >> 3);

#else

  u32* current = (u32*)trace_bits;
  u32* virgin  = (u32*)virgin_map;

  u32  i = (MAP_SIZE >> 2);

#endif /* ^__x86_64__ */

  u8   ret = 0;

//  for (u32 j = 0; j < MAP_SIZE; j++){
//    if (virgin_bits[j]) {
//      printf ("%d ", j);
//    }
//  }
//  printf("\n");
  
  while (i--) {

    /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
       that have not been already cleared from the virgin map - since this will
       almost always be the case. */

    if (unlikely(*current) && unlikely(*current & *virgin)) {

      if (likely(ret < 2)) {

        u8* cur = (u8*)current;
        u8* vir = (u8*)virgin;

        /* Looks like we have not found any new bytes yet; see if any non-zero
           bytes in current[] are pristine in virgin[]. */

#ifdef __x86_64__

        if ((cur[0] && vir[0] == 0xff) || (cur[1] && vir[1] == 0xff) ||
            (cur[2] && vir[2] == 0xff) || (cur[3] && vir[3] == 0xff) ||
            (cur[4] && vir[4] == 0xff) || (cur[5] && vir[5] == 0xff) ||
            (cur[6] && vir[6] == 0xff) || (cur[7] && vir[7] == 0xff)) ret = 2;
        else ret = 1;

#else

        if ((cur[0] && vir[0] == 0xff) || (cur[1] && vir[1] == 0xff) ||
            (cur[2] && vir[2] == 0xff) || (cur[3] && vir[3] == 0xff)) ret = 2;
        else ret = 1;

#endif /* ^__x86_64__ */

      }

      *virgin &= ~*current;

    }

    current++;
    virgin++;

  }


//  printf("After...\n");
//  for (u32 j = 0; j < MAP_SIZE; j++){
//    if (virgin_bits[j]) {
//      printf ("%d ", j);
//    }
//  }
// printf("\n");

  
  // if (ret && virgin_map == virgin_bits) bitmap_changed = 1;

  return ret;

}

CAMLprim value has_new_bits_aux(void) {
  return (Val_bool (has_new_bits(virgin_bits)));
}
