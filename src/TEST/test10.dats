#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"

fn test0(): void = {
  val t1 = $T.decode_utf80C_exn( $BS.pack "привет world")

  val () = assertloc( length t1 > 1)
  val second = t1[ i2sz 1]

  val () = assertloc( $BS.eq_bytestring_bytestringC( second, $BS.pack "р"))
  val () = free ((), () | second, t1)
  val () = free t1
}


implement main0() =
  ( test0()
  )
