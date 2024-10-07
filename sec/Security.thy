theory Security
  imports SecRGSep
begin

(*
  Do we need hiding here??
*)

datatype 'a aact = Tau | Vis 'a

type_synonym 'a hset = \<open>'a set set\<close>

definition secrel :: \<open>('s \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>secrel r \<equiv> reflp (curry r) \<and> symp (curry r)\<close>

definition secrel2hset :: \<open>('s \<times> 's \<Rightarrow> bool) \<Rightarrow> 's hset\<close> where
  \<open>secrel2hset r \<equiv> {{s'. \<exists>u. r (u,s')}|s. \<exists>u. r (s,u)}\<close>

definition hset2secrel :: \<open>'s hset \<Rightarrow> ('s \<times> 's \<Rightarrow> bool)\<close> where
  \<open>hset2secrel \<SS> \<equiv> \<lambda>(s,s'). \<exists>S\<in>\<SS>. s \<in> S \<and> s' \<in> S\<close>

(*
  Factorisation theorem?
*)

inductive seval :: \<open>'s hset \<times> ('s \<times> 's) comm \<Rightarrow> 'a aact \<Rightarrow> 's hset \<times> ('s \<times> 's) comm \<Rightarrow> bool\<close>
  (\<open>_ \<sim>_\<leadsto>\<^sub>s _\<close> [55, 0, 55] 56)
  where
  seqL: \<open>(\<SS>, c1) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1') \<Longrightarrow> (\<SS>, c1 ;; c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1' ;; c2)\<close>
| seqR: \<open>(\<SS>, Skip ;; c2) \<sim>\<tau>\<leadsto>\<^sub>s (\<SS>, c2)\<close>
| parL: \<open>(\<SS>, c1) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1') \<Longrightarrow> (\<SS>, c1 \<parallel> c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1' \<parallel> c2)\<close>
| parR: \<open>(\<SS>, c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c2') \<Longrightarrow> (\<SS>, c1 \<parallel> c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1 \<parallel> c2')\<close>
| indetL: \<open>(\<SS>, c1) \<sim>a\<leadsto>\<^sub>s (\<SS>', c1') \<Longrightarrow> (\<SS>, c1 \<^bold>+ c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c1')\<close>
| indetR: \<open>(\<SS>, c2) \<sim>a\<leadsto>\<^sub>s (\<SS>', c2') \<Longrightarrow> (\<SS>, c1 \<^bold>+ c2) \<sim>\<alpha>\<leadsto>\<^sub>s (\<SS>', c2')\<close>
| endetL: \<open>(\<SS>, c1) \<sim>Vis a\<leadsto>\<^sub>s (\<SS>', c1') \<Longrightarrow> (\<SS>, c1 \<box> c2) \<sim>Vis a\<leadsto>\<^sub>s (\<SS>', c1')\<close>
| endetR: \<open>(\<SS>, c2) \<sim>Vis a\<leadsto>\<^sub>s (\<SS>', c2') \<Longrightarrow> (\<SS>, c1 \<box> c2) \<sim>Vis a\<leadsto>\<^sub>s (\<SS>', c2')\<close>
| endetLtau: \<open>(\<SS>, c1) \<sim>Tau\<leadsto>\<^sub>s (\<SS>', c1') \<Longrightarrow> (\<SS>, c1 \<box> c2) \<sim>Tau\<leadsto>\<^sub>s (\<SS>', c1' \<box> c2)\<close>
| endetRtau: \<open>(\<SS>, c2) \<sim>Tau\<leadsto>\<^sub>s (\<SS>', c2') \<Longrightarrow> (\<SS>, c1 \<box> c2) \<sim>Tau\<leadsto>\<^sub>s (\<SS>', c1 \<box> c2')\<close>
| atom:
  \<open>\<SS>' = {({s1'. b (s1,s2) (s1',_)} \<union> {s1'. b (s1,s2) (_,s2')})|S s1 s2. S\<in>\<SS> \<and> s1 \<in> S \<and> s2 \<in> S} \<Longrightarrow>
    (\<SS>, \<langle>b\<rangle>) \<sim>Vis a\<leadsto>\<^sub>s (\<SS>', Skip)\<close>

(*
  | Atomic \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>\<close> [0] 999)
  | Iter \<open>'a comm\<close> (\<open>DO (_) OD\<close> [0] 999)
\<comment> \<open> loops are represented by (least) fixed points. Fixed point variables are done in de Brijn
style. \<close>
  | Fix \<open>'a comm\<close> (\<open>\<mu>\<close>)
  | FixVar nat
*)

end