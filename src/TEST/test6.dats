#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "./../HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"

fn test0(): void = {
  val i1 = $BS.pack "привет world"
  var t1: $T.Text0?
  val- true = $T.decode_utf80C( i1, t1)
  prval () = result_vt_unsuccess( t1)
  
  val env0 = ifold_left<$T.Text0><$BS.Bytestring1>( ($UN.cast{size_t} 0, $UN.cast{size_t} 0), t1, lam (idx, env, element) =<1>
      ((idx + 1, env.1 + length element), true) where {
        val () = $BS.println( element)
      }
  )
  val () = assertloc( env0.0 = 12)
  val () = assertloc( env0.1 = 18)
  val () = free t1
}


implement main0() =
  ( test0()
  )
