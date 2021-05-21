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
  var env0: size_t with env0_pf = $UN.cast{size_t} 0
  var env = (env0_pf | addr@ env0)
  
  val () = ifold_left<$T.Text0><$BS.Bytestring1>( env, t1, folder) where {
    fn
      folder
      {l:agz}
      ( idx: size_t
      , env: !( size_t @ l | ptr l)
      , element: !$BS.Bytestring1
      ):
      bool = true where {
        val (env1_pf | env1) = (env.0 | env.1)
        val () = !env1 := !env1 + 1
        prval () = env.0 := env1_pf
        val () = $BS.println( element)
      }
  }
  val (env0_pf1 | env0 ) = env
  prval () = env0_pf := env0_pf1
  val () = assertloc( !env0 = 12)
  val () = free t1
}


implement main0() =
  ( test0()
  )
