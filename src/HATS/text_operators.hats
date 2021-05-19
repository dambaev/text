

staload T="./../SATS/text.sats"

overload free with $T.free
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
