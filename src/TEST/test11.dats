#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"

fn test0(): void = {
  val t1 = $T.decode_utf80_normalizeC_exn( $BS.pack "привет world")
  val t2 = decode_utf8( $BS.pack "привет world")

  val () = assertloc( t1 = t2)
  val () = free t1
  val () = free t2
}


implement main0() =
  ( test0()
  )
