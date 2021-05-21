#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text_"

#define LIBS_targetloc "../libs" (* search path for external libs *)


#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
#include "./../HATS/text_operators.hats"
staload "./../SATS/text.sats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"
staload UN = "prelude/SATS/unsafe.sats"

fn
  {env:viewt0ype+}
  text_ifold_left
  {fe:eff}
  {len, bs_len, offset, cap, ucap, refcnt: nat | cap > 0}{dynamic:bool}{l:agz}
  ( env: INV(env)
  , i: !Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, l)
  , f: ( size_t, INV(env), !$BS.Bytestring1) -<fe> (env, bool)
  ):<fe,!wrt>
  env = result where {
  fun
    loop
    {len, offset: nat}
    .<len>.
    ( t: &$BS.Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l) >> [olen, ooffset: nat] $BS.Bytestring_vtype( olen, ooffset, cap, 0, 1, dynamic, l)
    , idx: size_t
    , env: env
    ):<fe,!wrt>
    env =
    let
      val t_sz = length t
    in
      if t_sz = 0
      then env
      else
      let
        val mblen = g1ofg0( bs_mb_head_bytes t)
      in
        if mblen <= 0
        then env (* i had already been checked for errors, so should not happen *)
        else
        let
          val mblen_sz = i2sz mblen (* cast to size_t *)
        in
          ifcase
          | mblen_sz > t_sz => env
          | mblen_sz > 4 => env
          | _ =>
          let
            val head = $BS.take( mblen_sz, t)
            val (new_env, is_continue) = f( idx, env, head)
            val () = free( head, t)
            val () = t := $BS.dropC( mblen_sz, t)
          in
            if is_continue
            then loop( t, idx + 1, new_env)
            else new_env
          end
        end
      end
    end
  var tmp: $BS.Bytestring0
  val () = tmp := $BS.ref_bs_parent i.2
  var acc: size_t?
  val result = loop( tmp, i2sz 0, env)
  val () = free( tmp, i.2)
}

// implementation of generic ifold_left
implement(env) ifold_left<Text0><$BS.Bytestring1><env>( env, i, f) =
let
  prval () = lemma_text_param i // bring type-properties into context
in
  ifcase
  | is_not_empty i => text_ifold_left<env>( env, i, f)
  | _ => env
end
