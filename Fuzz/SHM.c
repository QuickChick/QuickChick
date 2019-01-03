#include <sys/shm.h>
#include "alloc-inl.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>

static s32 shm_id;                    /* ID of the SHM region             */
u8* trace_bits;

#define MAP_SIZE_POW2       16
#define MAP_SIZE            (1 << MAP_SIZE_POW2)

static void remove_shm(void) {

  shmctl(shm_id, IPC_RMID, NULL);

}


void setup_shm(void) {

  u8* shm_str;

  //  if (!in_bitmap) memset(virgin_bits, 255, MAP_SIZE);

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

CAMLprim value setup_shm_prim(value unit)
{
  setup_shm();
  //  printf ("Setup succesful!\n");
  return Val_unit;
}

CAMLprim value copy_trace_bits( value ml_array )
{
    int i, len;
    len = Wosize_val(ml_array);
    for (i=0; i < len; i++)
    {
      //      caml_modify(&Field(ml_array, i), trace_bits[i]);
      if (i == 42) { caml_modify(&Field(ml_array, i), 42); }
    }

    return Val_unit ;
}

