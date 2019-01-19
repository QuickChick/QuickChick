let unlikely_branch =
  fun i ->
  if (0 < i)
  then if (i mod 100 == 0)
       then if (i mod 1000 == 0)
            then if (i mod 10000 == 0)
                 then if (i mod 100000 == 0)
                      then if (i mod 1000000 == 0)
                           then if (i < 1000001)
                                then failwith "bleh"
                                else 0
                           else 0
                      else 0
                 else 0
            else 0
       else 0
  else 0

