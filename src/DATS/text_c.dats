#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text_"

#define LIBS_targetloc "../libs" (* search path for external libs *)


#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
#include "./../HATS/text.hats"
staload "./../SATS/text.sats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload UN = "prelude/SATS/unsafe.sats"

implement free( i) = free bs where {
  val (_, _, bs) = i
}

implement free_shared( consume, preserve) = {
  val (_, _, bs) = consume
  val () = free( bs, preserve)
}

implement length( i) = i.0

extern fn
  u8_mblen
  {sz:nat}{l:agz}
  ( !array_v( uint8, l, sz)
  | ptr l
  , size_t sz
  ):<>
  int = "ext#"

extern fn
  u8_strnlen
  {sz:nat}{l:agz}
  ( !array_v( uint8, l, sz)
  | ptr l
  , size_t sz
  ):<>
  size_t = "ext#"

(* this function returns how many bytes occupies the first codepoint of bytestring *)
(* time: O(1), space: O(1) *)
fn
  bs_mb_head_bytes
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  ):
  int = result where {
  val (pf | i_p, i_sz) = $BS.bs2bytes_ro i
  prval () = to_bytes pf  where {
    extern prfn
      to_bytes
      {l:addr}{sz:nat}
      ( !array_v(char, l, sz) >> array_v( uint8, l, sz)
      ):<> void
  }
  val result = g1ofg0( u8_mblen( pf | i_p, i_sz)) (* now get the size of the first codepoint (head) in bytes *)
  prval () = to_char pf  where {
    extern prfn
      to_char
      {l:addr}{sz:nat}
      ( !array_v(uint8, l, sz) >> array_v( char, l, sz)
      ):<> void
  }
  prval () = $BS.bytes_addback( pf | i)
}

(* time: O(n), space: O(1) *)
fn
  bs_mb_length
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  , result: &size_t? >> opt( size_t, b)
  ):
  #[b:bool]
  bool(b) =
let
  fun
    loop
    {len, offset: nat}
    .<len>.
    ( t: &$BS.Bytestring_vtype( len, offset, bs_cap, 0, 1, bs_dynamic, bs_base) >> [olen, ooffset: nat] $BS.Bytestring_vtype( olen, ooffset, bs_cap, 0, 1, bs_dynamic, bs_base)
    , acc: size_t
    , acc_result: &size_t? >> opt( size_t, b)
    ):
    #[b:bool]
    bool(b) =
    let
      val t_sz = length t
    in
      if t_sz = 0
      then true where {
        val () = acc_result := acc
        prval () = opt_some( acc_result)
      }
      else 
      let
        val mblen = g1ofg0( bs_mb_head_bytes t)
      in
        if mblen <= 0
        then false where {
          prval () = opt_none( acc_result)
        }
        else
        let
          val mblen_sz = i2sz mblen (* cast to size_t *)
        in
          if mblen_sz > t_sz
          then false where {
            prval () = opt_none( acc_result)
          }
          else loop( t, acc + 1, acc_result) where {
            val () = t := $BS.dropC( mblen_sz, t)
          }
        end
      end
    end
  var tmp: $BS.Bytestring0
  val () = tmp := $BS.ref_bs_parent i
  var acc: size_t?
  val flag = loop( tmp, i2sz 0, acc)
  val () = free( tmp, i)
in
  if flag
  then flag where {
    prval () = opt_unsome( acc)
    val () = result := acc
    prval () = opt_some( result)
  }
  else flag where {
    prval () = opt_unnone( acc)
    prval () = opt_none( result)
  }
end


implement decode_utf80( i, result) =
let
  val i_sz = length i
  var i_mb_sz: size_t?
in
  if bs_mb_length (i, i_mb_sz) 
  then
  let
    prval () = opt_unsome( i_mb_sz)
  in
    ifcase
    | i_mb_sz < 0 => false where {
      prval () = result_failure( result)
      prval () = result_failure( i)
    }
    | i_mb_sz = i_sz => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 0u, $BS.ref_bs_parent i)
      prval () = result_success( result)
      prval () = result_success( i)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 1u, $BS.ref_bs_parent i)
      prval () = result_success( result)
      prval () = result_success( i)
    }
  end
  else false where {
    prval () = opt_unnone( i_mb_sz)
    prval () = result_failure( result)
    prval () = result_failure( i)
  }
end

implement decode_utf80C( i, result) =
let
  val i_sz = length i
  var i_mb_sz: size_t?
in
  if bs_mb_length (i, i_mb_sz) 
  then
  let
    prval () = opt_unsome( i_mb_sz)
  in
    ifcase
    | i_mb_sz < 0 => false where {
      prval () = result_failure( result)
      val () = free i
    }
    | i_mb_sz = i_sz => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 0u, i)
      prval () = result_success( result)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 1u, i)
      prval () = result_success( result)
    }
  end
  else false where {
    prval () = opt_unnone( i_mb_sz)
    prval () = result_failure( result)
    val () = free i
  }
end

implement decode_utf81( i) =
let
  var result: Text0?
in
  if decode_utf80( i, result)
  then Some_vt( result) where {
    prval () = result_unsuccess( result)
  }
  else None_vt() where {
    prval () = result_unfailure( result)
  }
end

implement decode_utf81C( i) =
let
  var result: Text0?
in
  if decode_utf80C( i, result)
  then Some_vt( result) where {
    prval () = result_unsuccess( result)
  }
  else None_vt() where {
    prval () = result_unfailure( result)
  }
end
