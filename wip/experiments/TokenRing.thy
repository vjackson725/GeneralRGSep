theory TokenRing
  imports "../RGLogic"
begin

definition \<open>upd_shared r \<equiv> \<lambda>(hl,hs) (hl',hs'). hl' = hl \<and> r hs hs'\<close>
definition \<open>upd_local r \<equiv> \<lambda>(hl,hs) (hl',hs'). r hl hl' \<and> hs' = hs\<close>

definition
  \<open>token_proc (i :: nat) (M :: nat)
      (turn :: 'y) (count :: 'y) (break :: 'x)
    :: (('x \<rightharpoonup> bool) \<times> ('y \<rightharpoonup> nat)) comm \<equiv>
    \<langle> upd_local (\<lambda>hl hl'. hl' = hl(break \<mapsto> \<bottom>)) \<rangle> ;;
    DO
      Guard (\<lambda>(hl,hs). \<not> the (hl break)) ;;
      Guard (\<lambda>(hl,hs). the (hs turn) = i) ;;
      (IfThenElse
        (\<lambda>(hl,hs). the (hs count) \<ge> 100)
        (\<langle> upd_shared (\<lambda>hs hs'. hs' = hs(turn \<mapsto> (the (hs turn) + 1) mod M)) \<rangle> ;;
          \<langle> upd_local (\<lambda>hl hl'. hl' = hl(break \<mapsto> \<top>)) \<rangle>)
        (\<langle> upd_shared (\<lambda>hs hs'. hs' = hs(count \<mapsto> the (hs count) + 1)) \<rangle> ;;
         \<langle> upd_shared (\<lambda>hs hs'. hs' = hs(turn \<mapsto> (the (hs turn) + 1) mod M)) \<rangle>)
      )
    OD\<close>

lemma
  \<open>token_ring turn count break \<equiv>
    token_proc 0 2 turn count break \<parallel>
    token_proc 1 2 turn count break\<close>
  oops

end