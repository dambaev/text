#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"

fn test0():void = {
  val i1 = $BS.pack "привет"
  val i2 = $BS.pack " world"
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80( i1, t1)
  val- true = $T.decode_utf80( i2, t2)
  prval () = result_unsuccess( i1)
  prval () = result_unsuccess( i2)
  prval () = result_unsuccess( t1)
  prval () = result_unsuccess( t2)
  
  val () = assertloc( length t1 > 0)
  val () = assertloc( length t2 > 0)
  val t = t1 !+! t2
  
  val () = assertloc( length t = 12)
  val () = free t
  val () = free( t1, i1)
  val () = free i1
  val () = free( t2, i2)
  val () = free i2
}
  
fn test1():void = {
  val i1 = $BS.pack "привет"
  val i2 = $BS.pack " world"
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80C( i1, t1)
  val- true = $T.decode_utf80C( i2, t2)
  prval () = result_unsuccess( t1)
  prval () = result_unsuccess( t2)

  val () = assertloc( length t1 > 0)
  val () = assertloc( length t2 > 0)
  val t = t1 + t2
  
  val () = assertloc( length t = 12)
  val () = free t
}
  

implement main0() =
  ( test0()
  ; test1()
  )
