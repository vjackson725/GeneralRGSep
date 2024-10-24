theory Lang
  imports SepAlgInstances
begin


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 'a comm =
  Skip
  | Seq \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Endet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<box>\<close> 65)
  \<comment> \<open> note we represent crashes by \<open>Inr ()\<close>, and not \<open>None\<close>, as options and either have different
        separation algebras. \<close>
  | Atomic \<open>'a \<Rightarrow> 'a + unit \<Rightarrow> bool\<close> (\<open>\<langle> _ \<rangle>\<close> [0] 999)
  | Iter \<open>'a comm\<close> (\<open>DO (_) OD\<close> [0] 999)
\<comment> \<open> loops are represented by (least) fixed points. Fixed point variables are done in de Bruijn
      style. \<close>
  | Fix \<open>'a comm\<close> (\<open>\<mu>\<close>)
  | FixVar nat

subsection \<open> substitution \<close>

primrec map_fixvar :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a comm \<Rightarrow> 'a comm\<close> where
  \<open>map_fixvar f Skip = Skip\<close>
| \<open>map_fixvar f (c1 ;; c2) = map_fixvar f c1 ;; map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<parallel> c2) = map_fixvar f c1 \<parallel> map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<^bold>+ c2) = map_fixvar f c1 \<^bold>+ map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<box> c2) = map_fixvar f c1 \<box> map_fixvar f c2\<close>
| \<open>map_fixvar f (DO c OD) = DO (map_fixvar f c) OD\<close>
| \<open>map_fixvar f (\<mu> c) = \<mu> (map_fixvar (case_nat 0 (Suc \<circ> f)) c)\<close>
| \<open>map_fixvar f (FixVar x) = FixVar (f x)\<close>
| \<open>map_fixvar f (Atomic b) = Atomic b\<close>


lemma map_fixvar_size[simp]:
  \<open>size (map_fixvar f c) = size c\<close>
  by (induct c arbitrary: f) force+

lemma map_fixvar_comp:
  \<open>map_fixvar f (map_fixvar g c) = map_fixvar (f \<circ> g) c\<close>
  by (induct c arbitrary: f g)
    (force intro: arg_cong2[where f=map_fixvar, OF _ refl] simp add: comp_def split: nat.splits)+

lemma map_fixvar_rev_iff:
  \<open>map_fixvar f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_fixvar f ca)\<close>
  \<open>map_fixvar f c = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = map_fixvar (case_nat 0 (Suc \<circ> f)) ca)\<close>
  \<open>map_fixvar f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_fixvar f c = FixVar y \<longleftrightarrow> (\<exists>x. c = FixVar x \<and> f x = y)\<close>
  \<open>map_fixvar f c = Atomic b \<longleftrightarrow> c = Atomic b\<close>
         apply ((induct c; simp), metis)
         apply ((induct c; simp), metis)
        apply ((induct c; simp), metis)
       apply ((induct c; simp), metis)
      apply ((induct c; simp), metis)
     apply ((induct c; simp), blast)
    apply (induct c; simp; fail)+
  done

lemmas map_fixvar_sym_rev_iff = map_fixvar_rev_iff[THEN trans[OF eq_commute]]

lemma map_fixvar_inj_inject:
  \<open>inj f \<Longrightarrow> (map_fixvar f c1 = map_fixvar f c2) = (c1 = c2)\<close>
proof (induct c1 arbitrary: c2 f)
  case (Fix c1)
  moreover have \<open>inj (case_nat 0 (Suc \<circ> f))\<close>
    using Fix.prems
    apply (clarsimp simp add: inj_def)
    apply (case_tac x; case_tac y; simp)
    done
  ultimately show ?case
    by (force simp add: map_fixvar_sym_rev_iff)
next
  case (FixVar x)
  then show ?case
    by (metis injD map_fixvar_rev_iff(8))
qed (force simp add: map_fixvar_sym_rev_iff)+


primrec fixvar_subst :: \<open>'a comm \<Rightarrow> nat \<Rightarrow> 'a comm \<Rightarrow> 'a comm\<close> (\<open>_[_ \<leftarrow> _]\<close> [1000, 0, 0] 1000) where
  \<open>Skip[_ \<leftarrow> _] = Skip\<close>
| \<open>(c1 ;; c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] ;; c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<parallel> c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<parallel> c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<^bold>+ c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<^bold>+ c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<box> c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<box> c2[x \<leftarrow> c'])\<close>
| \<open>(DO c OD)[x \<leftarrow> c'] = (DO c[x \<leftarrow> c'] OD)\<close>
| \<open>(\<mu> c)[x \<leftarrow> c'] = \<mu> (c[Suc x \<leftarrow> c'])\<close>
| \<open>(FixVar y)[x \<leftarrow> c'] = (if x = y then c' else FixVar y)\<close>
| \<open>(Atomic b)[_ \<leftarrow> _] = Atomic b\<close>

lemma fixvar_subst_rev_iff:
  \<open>c[x \<leftarrow> cx] = Skip \<longleftrightarrow> c = Skip \<or> c = FixVar x \<and> cx = Skip\<close>
  \<open>c[x \<leftarrow> cx] = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
    c = FixVar x \<and> cx = c1' ;; c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<parallel> c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<^bold>+ c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<box> c2'\<close>
  \<open>c[x \<leftarrow> cx] = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = ca[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = DO c' OD\<close>
  \<open>c[x \<leftarrow> cx] = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = ca[Suc x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = \<mu> c'\<close>
  \<open>c[x \<leftarrow> cx] = FixVar y \<longleftrightarrow> c = FixVar x \<and> cx = FixVar y \<or> x \<noteq> y \<and> c = FixVar y\<close>
  \<open>c[x \<leftarrow> cx] = Atomic b \<longleftrightarrow> c = Atomic b \<or> c = FixVar x \<and> cx = Atomic b\<close>
          apply (induct c; simp; fail)
         apply ((induct c; simp), metis)+
  apply (induct c; simp; fail)
  done

lemma fixvar_subst_over_map_avoid:
  \<open>\<forall>y. f y \<noteq> x \<Longrightarrow> (map_fixvar f c)[x \<leftarrow> cx] = map_fixvar f c\<close>
  apply (induct c arbitrary: x f)
        apply (simp; fail)+
   apply (drule_tac x=\<open>Suc x\<close> in meta_spec, drule_tac x=\<open>case_nat 0 (Suc \<circ> f)\<close> in meta_spec,
      clarsimp split: nat.splits)
  apply force
  done

subsection \<open> Map atoms \<close>

fun map_comm :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a comm \<Rightarrow> 'b comm\<close> where
  \<open>map_comm f Skip = Skip\<close>
| \<open>map_comm f (a ;; b) = map_comm f a ;; map_comm f b\<close>
| \<open>map_comm f (a \<parallel> b) = map_comm f a \<parallel> map_comm f b\<close>
| \<open>map_comm f (a \<^bold>+ b) = map_comm f a \<^bold>+ map_comm f b\<close>
| \<open>map_comm f (a \<box> b) = map_comm f a \<box> map_comm f b\<close>
| \<open>map_comm f (Atomic b) = Atomic (\<lambda>x y. b (f x) (map_suml f y))\<close>
| \<open>map_comm f (DO a OD) = DO map_comm f a OD\<close>
| \<open>map_comm f (\<mu> c) = \<mu> (map_comm f c)\<close>
| \<open>map_comm f (FixVar x) = FixVar x\<close>

lemma map_comm_rev_iff:
  \<open>map_comm f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_comm f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_comm f ca)\<close>
  \<open>map_comm f c = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = map_comm f ca)\<close>
  \<open>map_comm f c = FixVar x \<longleftrightarrow> c = FixVar x\<close>
  \<open>map_comm f c = Atomic b \<longleftrightarrow> (\<exists>b'. c = Atomic b' \<and> b = (\<lambda>x y. b' (f x) (map_suml f y)))\<close>
  by (induct c; simp; argo)+

lemmas map_comm_rev_iff2 = map_comm_rev_iff[THEN trans[OF eq_commute]]

subsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('a \<Rightarrow> 'a + unit \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Skip\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| indet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| endet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<box> c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (DO c OD)\<close>
| fixpt[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (\<mu> c)\<close>
| fixvar[iff]: \<open>all_atom_comm p (FixVar x)\<close>
| atom[intro!]: \<open>p b \<Longrightarrow> all_atom_comm p (Atomic b)\<close>

inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_indetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_endetE[elim!]: \<open>all_atom_comm p (c1 \<box> c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (DO c OD)\<close>
inductive_cases all_atom_comm_fixptE[elim!]: \<open>all_atom_comm p (\<mu> c)\<close>
inductive_cases all_atom_comm_fixvarE[elim!]: \<open>all_atom_comm p (FixVar x)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic b)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<box> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (DO c OD) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (\<mu> c) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (Atomic b) \<longleftrightarrow> p b\<close>
  by fastforce+

lemma all_atom_comm_pred_mono:
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p c \<Longrightarrow> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_pred_mono':
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p \<le> all_atom_comm q\<close>
  using all_atom_comm_pred_mono by auto

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq:
  \<open>all_atom_comm (p \<sqinter> q) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_pconj_eq[simp]:
  \<open>all_atom_comm (\<lambda>x. p x \<and> q x) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  by (induct c) force+

lemma all_atom_comm_pTrue_eq[simp]:
  \<open>all_atom_comm (\<lambda>x. True) c\<close>
  by (induct c) force+

lemma all_atom_comm_subst[simp]:
  \<open>all_atom_comm p c' \<Longrightarrow> all_atom_comm p (c[x \<leftarrow> c']) \<longleftrightarrow> all_atom_comm p c\<close>
  by (induct c arbitrary: x) force+

lemma all_atom_comm_subst_strong:
  \<open>all_atom_comm p c' - all_atom_comm p c \<Longrightarrow> all_atom_comm p (c[x \<leftarrow> c']) \<longleftrightarrow> all_atom_comm p c\<close>
  by (induct c arbitrary: x) force+

abbreviation \<open>atoms_subrel_of r \<equiv> all_atom_comm (\<lambda>b. b \<le> r)\<close>


section \<open> Specific Languages \<close>

subsection \<open> Sugared atomic programs \<close>

subsubsection \<open> Assert \<close>

definition \<open>passert p \<equiv> \<lambda>a b. if p a then b = Inl a else b = Inr ()\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>

lemmas Assert_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passert_def]]


subsubsection \<open> Assume \<close>

definition \<open>passume p \<equiv> \<lambda>a b. p a \<and> b = Inl a\<close>

abbreviation \<open>Assume p \<equiv> Atomic (passume p)\<close>

lemmas Assume_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passume_def]]

lemma passume_simps[simp]:
  \<open>passume p a b \<longleftrightarrow> p a \<and> b = Inl a\<close>
  by (force simp add: passume_def)


subsection \<open> If-then-else and While Loops \<close>

definition \<open>IfThenElse p ct cf \<equiv> Assume p ;; ct \<box> Assume (-p) ;; cf\<close>
definition \<open>WhileLoop p c \<equiv> DO (Assume p ;; c \<box> Assume (-p)) OD\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def passume_def fun_eq_iff, blast)

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def map_fixvar_inj_inject passume_def fun_eq_iff, blast)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> \<mu> c\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>\<mu> c \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic b \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>Atomic b \<noteq> WhileLoop p c\<close>
  \<open>WhileLoop p c \<noteq> \<mu> c\<close>
  \<open>\<mu> c \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def; fail)+


end