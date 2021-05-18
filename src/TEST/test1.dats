#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
  
#include "HATS/text.hats"
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"

implement main0() = {
  val bs = $BS.pack "привет world"
  val () = assertloc( length bs = 18)
  val () = $BS.free bs
}