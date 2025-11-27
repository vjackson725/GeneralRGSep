theory Security
  imports "../RGLogic"
begin

(*
  Do we need hiding here??
*)

datatype 'a aact = Tau | Vis 'a

type_synonym 'a hset = \<open>'a set set\<close>

definition secrel :: \<open>('s \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>secrel r \<equiv> reflp (curry r) \<and> symp (curry r)\<close>

definition secrel2hset :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's hset\<close> where
  \<open>secrel2hset r \<equiv> {{s'. \<exists>u. r u s'}|s. \<exists>u. r s u}\<close>

definition hset2secrel :: \<open>'s hset \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool)\<close> where
  \<open>hset2secrel \<SS> \<equiv> \<lambda>s s'. \<exists>S\<in>\<SS>. s \<in> S \<and> s' \<in> S\<close>

definition rel_restrict :: \<open>'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> (infix \<open>\<restriction>\<^sub>R\<close> 70) where
  \<open>A \<restriction>\<^sub>R r \<equiv> \<lambda>x y. x \<in> A \<and> y \<in> A \<and> r x y\<close>

definition quad_exch :: \<open>('a \<times> 'b) \<times> ('c \<times> 'd) \<Rightarrow> ('a \<times> 'c) \<times> ('b \<times> 'd)\<close> where
  \<open>quad_exch \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

lemma quad_exch_idem[simp]:
  \<open>quad_exch (quad_exch x) = x\<close>
  unfolding quad_exch_def
  by (simp split: prod.splits)

(*
  Factorisation theorem?
*)

text \<open>
  It's obvious (from \<open>safe\<close>) that if you reach the end, then you satifsy the postcondition.
  The postcondition is supposed to encode all the knowledge information the attacker gains
  in the execution. Thus, the only thing remaining is to somehow capture a measure
  of the 'knowledge gained' at each step, and show that every assertions correctly
  represents it.
    This is almost trivial for atomic steps; what's left is control flow.

  We really want to justify things using observation-traces.
\<close>

definition \<open>pmerge xs ys \<equiv> undefined\<close>

\<comment> \<open>
  b (s,s) (s',s') should be the same as b (s,s) (s',_), if b is wf.
\<close>

definition
  \<open>ifpred p \<equiv> quasireflp (curry p) \<and> symp (curry p)\<close>


type_synonym ('l,'s) ifrgst = \<open>('l \<times> 'l) \<times> ('s \<times> 's)\<close>

lemma infoflow_soundness_v2:
  fixes r g :: \<open>'s::perm_alg \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
    and p q :: \<open>('l::perm_alg,'s) ifrgst \<Rightarrow> bool\<close>
    and c :: \<open>(('l,'s) ifrgst) comm\<close>
    and s1 s2 s1' s2' :: \<open>'l \<times> 's\<close>
  shows
  \<open>r, g \<turnstile>\<^bsub>\<top>\<^esub> { p } c { q } \<Longrightarrow>
    ifpred (p \<circ> quad_exch) \<Longrightarrow>
    (p \<circ> quad_exch) (s1, s2) \<Longrightarrow>
    bigtr (map_comm quad_exch c) s1 (t, s1') \<Longrightarrow>
    bigtr (map_comm quad_exch c) s2 (t, s2') \<Longrightarrow>
    (q \<circ> quad_exch) (s1', s2')\<close>
  sorry



end