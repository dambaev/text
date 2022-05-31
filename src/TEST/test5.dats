#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"

fn test0(): void = {
  val i1 = $BS.pack "привет world"
  val i2 = $BS.pack "привет world"
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80C( i1, t1)
  val- true = $T.decode_utf80C( i2, t2)
  prval () = result_vt_unsuccess( t1)
  prval () = result_vt_unsuccess( t2)
  val () = assertloc( t1 == t2)
  val () = free t1
  val () = free t2
}

fn test1():void = {
  val i1 = $BS.pack "привет"
  val i2 = $BS.pack " world"
  val i = $BS.pack "привет world"
  
  val t0 = $T.create( i2sz 256)
  var original: $T.Text0?
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80( i, original)
  val- true = $T.decode_utf80( i1, t1)
  val- true = $T.decode_utf80( i2, t2)
  prval () = result_vt_unsuccess( i)
  prval () = result_vt_unsuccess( i1)
  prval () = result_vt_unsuccess( i2)
  prval () = result_vt_unsuccess( original)
  prval () = result_vt_unsuccess( t1)
  prval () = result_vt_unsuccess( t2)
  
  val () = assertloc( length t1 > 0)
  val () = assertloc( length t2 > 0)
  val t = t0 ++! t1 ++! t2
  
  val () = assertloc( length t = 12)
  val () = assertloc( original == t)
  val () = free (() | original, i)
  val () = free i
  val () = free t
  val () = free( () | t1, i1)
  val () = free i1
  val () = free( () | t2, i2)
  val () = free i2
}
  
fn test2():void = {
  val i1 = $BS.pack "привет"
  val i2 = $BS.pack " world"

  val t0 = $T.create( i2sz 256)
  var t1: $T.Text0?
  var t2: $T.Text0?
  val- true = $T.decode_utf80C( i1, t1)
  val- true = $T.decode_utf80C( i2, t2)
  prval () = result_vt_unsuccess( t1)
  prval () = result_vt_unsuccess( t2)

  val () = assertloc( length t1 > 0)
  val () = assertloc( length t2 > 0)
  val t = t0 ++ t1 ++ t2
  
  val () = assertloc( length t = 12)
  val () = free t
}

fn test3(): void = {
  val e1 = $T.empty()
  val e2 = $T.empty()
  val e3 = $T.create( i2sz 10)
  val () = assertloc( e1 == e2)
  val () = assertloc( e1 == e3)
  val () = free e1
  val () = free e2
  val () = free e3
}

implement main0() =
  ( test0()
  ; test1()
  ; test2()
  ; test3()
  )
