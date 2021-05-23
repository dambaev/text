

staload T="./../SATS/text.sats"

overload free with $T.free
overload free with $T.free_shared_t_bs
overload free with $T.free_shared_bs_t
overload free with $T.free_shared
overload length with $T.length

(* append operators *)
overload + with $T.append_tC_tC
overload !+! with $T.append_t_t
overload !+ with $T.append_t_tC
overload +! with $T.append_tC_t

(* grow operators *)
overload ++ with $T.grow_tC_tC
overload ++! with $T.grow_tC_t

(* comparison *)
overload = with $T.eq_t_t
overload == with $T.eq_t_t
overload =@ with $T.eq_t_tC
overload ==@ with $T.eq_t_tC
overload <> with $T.not_eq_t_t
overload <>@ with $T.not_eq_t_tC
overload != with $T.not_eq_t_t
overload !=@ with $T.not_eq_t_tC

(* get_at *)
overload [] with $T.get_at_uint
overload [] with $T.get_at_int
