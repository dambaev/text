#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"

fn test0(): void = {
  val i1 = $BS.pack "привет world"
  val i2 = $BS.pack "world"
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80C( i1, t1)
  val- true = $T.decode_utf80C( i2, t2)
  prval () = result_vt_unsuccess( t1)
  prval () = result_vt_unsuccess( t2)
  
  val () = assertloc( i2sz 7 < length t1)
  val t = $T.drop( i2sz 7, t1)
  val () = assertloc( length t.2 > 0)
  val () = assertloc( t == t2)
  val () = free (t, t1)
  val () = free t1
  val () = free t2
}


implement main0() =
  ( test0()
  )
