#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"

fn test0():void = {
  val i = $BS.pack "привет world"
  var bs: $T.Text0?
  val- true = $T.decode_utf80( i, bs)
  prval () = result_vt_unsuccess( bs)
  prval () = result_vt_unsuccess( i)
  val () = assertloc( $T.length bs = 12)
  val () = free( bs, i)
  val () = free i
}
  
fn test1():void = {
  val i = $BS.pack "привет world"
  var bs: $T.Text0?
  val- true = $T.decode_utf80C( i, bs)
  prval () = result_vt_unsuccess( bs)
  val () = assertloc( $T.length bs = 12)
  val () = free bs
}

implement main0() =
  ( test0()
  ; test1()
  )
