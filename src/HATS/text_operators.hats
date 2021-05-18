

staload T="./../SATS/text.sats"

overload free with $T.free
overload free with $T.free_shared
overload length with $T.length

overload !+! with $T.append_t_t
overload + with $T.append_tC_tC