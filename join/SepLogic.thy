theory SepLogic
  imports JoinAlg
begin

(*
text \<open>
  This file implements a hierarchy of typeclasses for resource algebras.
  This is inspired by Klein et. al's [KKB2012] Isabelle/HOL separation algebra typeclasses
  and Appel et. al.'s [VSTBook2014] typeclass hierarchy in Coq.
\<close>

section \<open> Common Notions \<close>

class disjoint =
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>#\<^sub>J\<close> 60)
begin

abbreviation ndisjoint (infix \<open>#'/#\<close> 60) where
  \<open>a #/# b \<equiv> \<not> a #\<^sub>J b\<close>

end

section \<open> Algebras \<close>

subsection \<open> Pre-permission algebras \<close>

class pre_perm_alg = disjoint +\<^sub>J plus +
  (* partial commutative monoid *)
  assumes partial_add_assoc: \<open>a #\<^sub>J b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> (a +\<^sub>J b) +\<^sub>J c = a +\<^sub>J (b +\<^sub>J c)\<close>
  assumes partial_add_commute: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b +\<^sub>J a\<close>
  assumes disjoint_sym: \<open>a #\<^sub>J b \<Longrightarrow> b #\<^sub>J a\<close>
  assumes disjoint_add_rightL: \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> a #\<^sub>J b\<close>
  assumes disjoint_add_right_commute: \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> b #\<^sub>J a +\<^sub>J c\<close>
  (* non-negative *)
(*
  assumes non_negative:
    \<open>w #\<^sub>J z \<Longrightarrow>
      \<exists>x. w +\<^sub>J z #\<^sub>J x \<Longrightarrow>
      (\<forall>x. w +\<^sub>J z #\<^sub>J x \<longrightarrow> w +\<^sub>J z +\<^sub>J x = x) \<Longrightarrow>
      w #\<^sub>J x \<Longrightarrow> w +\<^sub>J x = x\<close>
*)
begin

lemma disjoint_sym_iff: \<open>a #\<^sub>J b \<longleftrightarrow> b #\<^sub>J a\<close>
  using disjoint_sym by blast

lemma disjoint_add_rightR: \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemmas disjoint_add_rightR' =
  disjoint_add_rightR[OF disjoint_sym, THEN disjoint_sym, of c b a for a b c]

lemma disjoint_add_leftL: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  using disjoint_add_rightL disjoint_sym by blast

lemma disjoint_add_leftR: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> b #\<^sub>J c\<close>
  by (metis disjoint_add_leftL disjoint_sym partial_add_commute)

lemma disjoint_add_right_commute2:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> c #\<^sub>J b +\<^sub>J a\<close>
  by (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma disjoint_add_left_commute:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> c +\<^sub>J b #\<^sub>J a\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute)

lemma disjoint_add_left_commute2:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> a +\<^sub>J c #\<^sub>J b\<close>
  by (metis disjoint_add_leftR disjoint_add_left_commute partial_add_commute)

lemma disjoint_add_swap_rl:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> a +\<^sub>J b #\<^sub>J c\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute partial_add_commute)

lemma disjoint_add_swap_rl2:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> a +\<^sub>J c #\<^sub>J b\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute partial_add_commute)

lemma disjoint_add_swap_lr:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c\<close>
  by (simp add: disjoint_add_right_commute2 disjoint_sym_iff partial_add_commute)

lemma disjoint_add_swap_lr2:
  \<open>a #\<^sub>J c \<Longrightarrow> a +\<^sub>J c #\<^sub>J b \<Longrightarrow> a #\<^sub>J b +\<^sub>J c\<close>
  by (metis disjoint_add_left_commute disjoint_sym_iff)

lemma disjoint_middle_swap:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> a +\<^sub>J b +\<^sub>J c #\<^sub>J d \<Longrightarrow> a +\<^sub>J c #\<^sub>J b +\<^sub>J d\<close>
  by (metis disjoint_add_leftR disjoint_add_right_commute2 disjoint_add_swap_lr disjoint_sym_iff
      partial_add_assoc)

lemma disjoint_middle_swap2:
  \<open>b #\<^sub>J c \<Longrightarrow> b +\<^sub>J c #\<^sub>J d \<Longrightarrow> a #\<^sub>J b +\<^sub>J c +\<^sub>J d \<Longrightarrow> a +\<^sub>J c #\<^sub>J b +\<^sub>J d\<close>
  by (metis disjoint_add_rightR disjoint_add_right_commute2 disjoint_add_rightL partial_add_assoc
      partial_add_commute)

lemma partial_add_left_commute:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> b +\<^sub>J (a +\<^sub>J c) = a +\<^sub>J (b +\<^sub>J c)\<close>
  by (metis partial_add_assoc partial_add_commute disjoint_sym)

lemma partial_add_left_commute2:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> b +\<^sub>J (a +\<^sub>J c) = a +\<^sub>J (b +\<^sub>J c)\<close>
  by (metis partial_add_left_commute disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_right_commute:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a +\<^sub>J b +\<^sub>J c = a +\<^sub>J c +\<^sub>J b\<close>
  by (simp add: disjoint_sym partial_add_assoc partial_add_commute)

lemma partial_add_assoc_commute_left:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> b +\<^sub>J a +\<^sub>J c = a +\<^sub>J (b +\<^sub>J c)\<close>
  by (metis partial_add_assoc partial_add_commute)

lemma partial_add_assoc_commute_right:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a +\<^sub>J c +\<^sub>J b = a +\<^sub>J (b +\<^sub>J c)\<close>
  by (metis partial_add_commute partial_add_assoc_commute_left partial_add_right_commute)

lemma partial_add_assoc2:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<Longrightarrow> (a +\<^sub>J b) +\<^sub>J c = a +\<^sub>J (b +\<^sub>J c)\<close>
  using disjoint_add_leftL disjoint_add_leftR partial_add_assoc by blast

lemma partial_add_assoc3:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> (a +\<^sub>J b) +\<^sub>J c = a +\<^sub>J (b +\<^sub>J c)\<close>
  by (meson disjoint_add_rightR disjoint_add_rightL partial_add_assoc)

lemma partial_add_double_assoc:
  \<open>a #\<^sub>J c \<Longrightarrow> b #\<^sub>J d \<Longrightarrow> c #\<^sub>J d \<Longrightarrow> b #\<^sub>J c +\<^sub>J d \<Longrightarrow> a #\<^sub>J b +\<^sub>J (c +\<^sub>J d) \<Longrightarrow> a +\<^sub>J b +\<^sub>J (c +\<^sub>J d) = (a +\<^sub>J c) +\<^sub>J (b +\<^sub>J d)\<close>
  by (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute partial_add_assoc
      partial_add_left_commute)


subsubsection \<open> order \<close>

text \<open>
  Resources give rise to a natural order, but it's not the same as standard
  order implementations unless all elements have a unit.
\<close>

text \<open>
  The 'part_of' relation is almost an order, except that it doesn't satisfy reflexivity.
\<close>

definition part_of :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<lesssim>\<close> 50) where
  \<open>a \<lesssim> b \<equiv> \<exists>c. a #\<^sub>J c \<and> a +\<^sub>J c = b\<close>

definition less_eq_sepadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<close> 50) where
  \<open>(\<preceq>) \<equiv> \<lambda>a b. a = b \<or> (\<exists>c. a #\<^sub>J c \<and> a +\<^sub>J c = b)\<close>

definition less_sepadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<close> 50) where
  \<open>(\<prec>) \<equiv> \<lambda>a b. a \<noteq> b \<and> (\<exists>c. a #\<^sub>J c \<and> a +\<^sub>J c = b) \<and> \<not> (\<exists>c. b #\<^sub>J c \<and> b +\<^sub>J c = a)\<close>

abbreviation (input) greater_eq_sepadd  (infix \<open>\<succeq>\<close> 50)
  where \<open>(\<succeq>) \<equiv> \<lambda>x y. (\<preceq>) y x\<close>

abbreviation (input) greater_sepadd (infix \<open>\<succ>\<close> 50)
  where \<open>(\<succ>) \<equiv> \<lambda>x y. (\<prec>) y x\<close>

lemma part_of_trans[trans]:
  \<open>a \<lesssim> b \<Longrightarrow> b \<lesssim> c \<Longrightarrow> a \<lesssim> c\<close>
  by (fastforce dest: disjoint_add_swap_lr simp add: part_of_def partial_add_assoc2)

sublocale resource_preordering: preordering \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  apply standard
    apply (force simp add: less_eq_sepadd_def)
   apply (fastforce dest: disjoint_add_swap_lr simp add: less_eq_sepadd_def partial_add_assoc2)
  apply (force simp add: less_eq_sepadd_def less_sepadd_def)
  done

sublocale resource_preorder: preorder \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  by standard
    (force dest: resource_preordering.trans
      simp add: resource_preordering.strict_iff_not
                resource_preordering.refl)+

lemma partial_le_plus: \<open>a #\<^sub>J b \<Longrightarrow> a \<preceq> a +\<^sub>J b\<close>
  by (meson less_eq_sepadd_def part_of_def)

lemma partial_le_plus2: \<open>a #\<^sub>J b \<Longrightarrow> b \<preceq> a +\<^sub>J b\<close>
  by (metis partial_le_plus disjoint_sym partial_add_commute)

lemma partial_le_part_left: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b \<preceq> c \<Longrightarrow> a \<preceq> c\<close>
  using resource_preordering.trans partial_le_plus by blast

lemma partial_le_part_right: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b \<preceq> c \<Longrightarrow> b \<preceq> c\<close>
  using resource_preordering.trans partial_le_plus2 by blast

lemma common_subresource_selfsep:
  \<open>a #\<^sub>J b \<Longrightarrow> ab \<preceq> a \<Longrightarrow> ab \<preceq> b \<Longrightarrow> ab #\<^sub>J ab\<close>
  by (metis disjoint_add_rightL disjoint_sym less_eq_sepadd_def)

lemma selfdisjoint_over_selfdisjoint:
  \<open>a #\<^sub>J a \<Longrightarrow> \<forall>x. x \<preceq> a \<longrightarrow> x #\<^sub>J x\<close>
  using common_subresource_selfsep by blast

lemma disjoint_preservation:
  \<open>a' \<preceq> a \<Longrightarrow> a #\<^sub>J b \<Longrightarrow> a' #\<^sub>J b\<close>
  by (metis disjoint_add_rightL disjoint_sym less_eq_sepadd_def)

lemma disjoint_preservation2:
  \<open>b' \<preceq> b \<Longrightarrow> a #\<^sub>J b \<Longrightarrow> a #\<^sub>J b'\<close>
  using disjoint_preservation disjoint_sym by blast

lemma sepadd_left_mono:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b \<preceq> c \<Longrightarrow> a +\<^sub>J b \<preceq> a +\<^sub>J c\<close>
  by (metis disjoint_add_swap_rl less_eq_sepadd_def partial_add_assoc3)

lemma sepadd_right_mono:
  \<open>a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a \<preceq> b \<Longrightarrow> a +\<^sub>J c \<preceq> b +\<^sub>J c\<close>
  by (metis disjoint_sym_iff partial_add_commute sepadd_left_mono)

lemma sepadd_mono:
  \<open>a #\<^sub>J b \<Longrightarrow> c #\<^sub>J d \<Longrightarrow> a \<preceq> c \<Longrightarrow> b \<preceq> d  \<Longrightarrow> a +\<^sub>J b \<preceq> c +\<^sub>J d\<close> 
  by (meson disjoint_preservation resource_preorder.order_trans sepadd_left_mono sepadd_right_mono)

lemma no_disjoint_then_maximal_resource:
  \<open>(\<forall>y. \<not> x #\<^sub>J y) \<Longrightarrow> (\<forall>y. \<not> y \<succ> x)\<close>
  using less_sepadd_def by presburger


subsubsection \<open> sepadd_unit \<close>

definition \<open>sepadd_unit a \<equiv> (\<exists>b. a #\<^sub>J b) \<and> (\<forall>b. a #\<^sub>J b \<longrightarrow> a +\<^sub>J b = b)\<close>

lemma sepadd_unitI[intro]:
  \<open>a #\<^sub>J b \<Longrightarrow> (\<And>b. a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b) \<Longrightarrow> sepadd_unit a\<close>
  using sepadd_unit_def by blast

lemma sepadd_unitE[elim]:
  \<open>sepadd_unit a \<Longrightarrow> (\<And>b. a #\<^sub>J b \<Longrightarrow> (\<And>b. a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using sepadd_unit_def by blast

lemma sepadd_unitD:
  \<open>sepadd_unit a \<Longrightarrow> \<exists>b. a #\<^sub>J b\<close>
  \<open>sepadd_unit a \<Longrightarrow> a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b\<close>
  by blast+

abbreviation \<open>sepadd_units \<equiv> Collect sepadd_unit\<close>

lemma units_are_selfdisjoint:
  \<open>(\<forall>b. a #\<^sub>J b \<longrightarrow> a +\<^sub>J b = b) \<Longrightarrow> a #\<^sub>J b \<Longrightarrow> a #\<^sub>J a\<close>
  by (metis disjoint_add_rightL)

lemma sepadd_unit_selfsep[dest]:
  \<open>sepadd_unit a \<Longrightarrow> a #\<^sub>J a\<close>
  using units_are_selfdisjoint sepadd_unit_def
  by blast

lemma sepadd_unit_def_strong:
  \<open>sepadd_unit a \<longleftrightarrow> a #\<^sub>J a \<and> (\<forall>b. a #\<^sub>J b \<longrightarrow> a +\<^sub>J b = b)\<close>
  by blast

lemma sepadd_unit_idem_add[simp]: \<open>sepadd_unit u \<Longrightarrow> u +\<^sub>J u = u\<close>
  using sepadd_unit_def units_are_selfdisjoint by auto

lemmas sepadd_unit_left = sepadd_unitD(2)

lemma sepadd_unit_right: \<open>sepadd_unit u \<Longrightarrow> a #\<^sub>J u \<Longrightarrow> a +\<^sub>J u = a\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_left)

lemma disjoint_units_identical:
  \<open>a #\<^sub>J b \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_def)

lemma related_units_disjoint:
  \<open>sepadd_unit u1 \<Longrightarrow> sepadd_unit u2 \<Longrightarrow> a #\<^sub>J u1 \<Longrightarrow> a #\<^sub>J u2 \<Longrightarrow> u1 #\<^sub>J u2\<close>
  by (metis disjoint_add_leftL disjoint_sym sepadd_unit_def)

lemma related_units_identical:
  \<open>sepadd_unit u1 \<Longrightarrow> sepadd_unit u2 \<Longrightarrow> a #\<^sub>J u1 \<Longrightarrow> a #\<^sub>J u2 \<Longrightarrow> u2 = u1\<close>
  using related_units_disjoint disjoint_units_identical by blast

lemma trans_disjoint_units_identical:
  \<open>a #\<^sub>J b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit c \<Longrightarrow> a = c\<close>
  by (metis disjoint_sym related_units_identical)


subsubsection \<open> Pseudo-units \<close>

text \<open> Pseudo-units: 'units' for certain resources. Can be non-unital for other resources. \<close>
definition \<open>sepadd_punit_of u x \<equiv> u #\<^sub>J x \<and> u +\<^sub>J x = x\<close>

lemma wunit_is_punit: \<open>sepadd_unit u \<Longrightarrow> Ex (sepadd_punit_of u)\<close>
  using sepadd_punit_of_def sepadd_unit_def by blast

lemma sepadd_punit_of_unit_res_mono:
  \<open>x \<preceq> y \<Longrightarrow> sepadd_punit_of a x \<Longrightarrow> sepadd_punit_of a y\<close>
  by (metis disjoint_add_swap_lr less_eq_sepadd_def partial_add_assoc3 sepadd_punit_of_def)

lemma sepadd_punit_of_unit_res_mono':
  \<open>x \<preceq> y \<Longrightarrow> a #\<^sub>J x \<Longrightarrow> a +\<^sub>J x = x \<Longrightarrow> a #\<^sub>J y \<and> a +\<^sub>J y = y\<close>
  using sepadd_punit_of_unit_res_mono
  by (simp add: sepadd_punit_of_def)


subsubsection \<open> Absorbing Resources \<close>

definition \<open>sepadd_absorb a \<equiv> \<forall>b. a #\<^sub>J b \<longrightarrow> a +\<^sub>J b = a\<close>

lemma above_zero_impl_zero:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_absorb a \<Longrightarrow> sepadd_absorb b\<close>
  by (metis less_eq_sepadd_def sepadd_absorb_def)

lemma zeros_add_to_zero:
  \<open>x #\<^sub>J y \<Longrightarrow> sepadd_absorb x \<Longrightarrow> sepadd_absorb (x +\<^sub>J y)\<close>
  by (simp add: sepadd_absorb_def)

lemma disjoint_absorb_res_then_res_leq:
  assumes \<open>sepadd_absorb w\<close>
  shows \<open>a #\<^sub>J w \<Longrightarrow> a \<preceq> w\<close>
  by (metis assms disjoint_sym_iff partial_le_plus2 sepadd_absorb_def)

lemma disjoint_absorb_res_then_disjoint_subres:
  assumes \<open>sepadd_absorb w\<close>
  shows \<open>a #\<^sub>J w \<Longrightarrow> b #\<^sub>J w \<Longrightarrow> a #\<^sub>J b\<close>
  using assms disjoint_absorb_res_then_res_leq disjoint_preservation2
  by blast


subsubsection \<open> duplicable \<close>

lemma add_to_selfsep_preserves_selfsep: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = c \<Longrightarrow> c #\<^sub>J c \<Longrightarrow> a #\<^sub>J a\<close>
  by (meson disjoint_add_rightL disjoint_sym)

lemma add_to_selfsep_preserves_selfsepR: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = c \<Longrightarrow> c #\<^sub>J c \<Longrightarrow> b #\<^sub>J b\<close>
  using disjoint_sym partial_add_commute add_to_selfsep_preserves_selfsep by blast

definition \<open>sepadd_dup a \<equiv> a #\<^sub>J a \<and> a +\<^sub>J a = a\<close>

lemma units_are_dup: \<open>sepadd_unit a \<Longrightarrow> sepadd_dup a\<close>
  by (simp add: sepadd_unit_selfsep sepadd_dup_def)


subsubsection \<open>sepdomeq\<close>

definition sepdomeq (infix \<open>=\<^sub>#\<close> 55) where
  \<open>sepdomeq a b \<equiv> \<forall>c. a #\<^sub>J c = b #\<^sub>J c\<close>

lemma sepdomeq_reflI[intro!]:
  \<open>sepdomeq a a\<close>
  by (simp add: reflpI sepdomeq_def)

lemma sepdomeq_reflp:
  \<open>reflp sepdomeq\<close>
  by (simp add: reflpI sepdomeq_def)

lemma sepdomeq_sym:
  \<open>sepdomeq a b \<Longrightarrow> sepdomeq b a\<close>
  by (metis sepdomeq_def)

lemma sepdomeq_symp:
  \<open>symp sepdomeq\<close>
  by (metis sepdomeq_def sympI)

lemma sepdomeq_trans[trans]:
  \<open>sepdomeq a b \<Longrightarrow> sepdomeq b c \<Longrightarrow> sepdomeq a c\<close>
  by (simp add: sepdomeq_def)

lemma sepdomeq_transp:
  \<open>transp sepdomeq\<close>
  by (simp add: sepdomeq_def transp_def)

lemma same_sepdom_disjoint_leftD:
  \<open>sepdomeq a b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c\<close>
  by (simp add: sepdomeq_def)

lemma sepdomeq_disjoint_rightD:
  \<open>sepdomeq a b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  by (simp add: sepdomeq_def)

definition sepdom_leq (infix \<open>\<preceq>\<^sub>#\<close> 55) where
  \<open>a \<preceq>\<^sub># b \<equiv> \<forall>c. b #\<^sub>J c \<longrightarrow> a #\<^sub>J c\<close>

lemma sepdom_leq_reflp:
  \<open>reflp (\<preceq>\<^sub>#)\<close>
  by (simp add: reflpI sepdom_leq_def)

lemma sepdom_leq_transp:
  \<open>transp (\<preceq>\<^sub>#)\<close>
  by (simp add: sepdom_leq_def transp_def)

lemma sepdom_leq_disjointD:
  \<open>a \<preceq>\<^sub># b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  by (simp add: sepdom_leq_def)

lemma sepdom_leq_antisym:
  \<open>a \<preceq>\<^sub># b \<Longrightarrow> b \<preceq>\<^sub># a \<Longrightarrow> a =\<^sub># b\<close>
  using sepdomeq_def sepdom_leq_def by blast

lemma resleq_implies_sepdom_leq:
  \<open>lb \<preceq> la \<Longrightarrow> lb \<preceq>\<^sub># la\<close>
  by (force simp add: sepdom_leq_def dest: disjoint_preservation)


subsubsection \<open> Cancellative resources \<close>

definition
  \<open>cancellative c \<equiv>
    \<forall>a b. a #\<^sub>J c \<longrightarrow> b #\<^sub>J c \<longrightarrow> a +\<^sub>J c = b +\<^sub>J c \<longrightarrow> a = b\<close>

lemma cancellativeD:
  \<open>cancellative c \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a +\<^sub>J c = b +\<^sub>J c \<Longrightarrow> a = b\<close>
  using cancellative_def by simp

end


subsection \<open> Permission Algebras \<close>


class positivity_law = disjoint +\<^sub>J plus +
  assumes positivity:
    \<open>a #\<^sub>J c1 \<Longrightarrow> a +\<^sub>J c1 = b \<Longrightarrow> b #\<^sub>J c2 \<Longrightarrow> b +\<^sub>J c2 = a \<Longrightarrow> a = b\<close>

class perm_alg = pre_perm_alg +\<^sub>J positivity_law
begin

text \<open> This lemma is just positivity stated another way. \<close>
lemma part_of_antisym:
  \<open>a \<lesssim> b \<Longrightarrow> b \<lesssim> a \<Longrightarrow> a = b\<close>
  using positivity part_of_def by auto

lemma less_sepadd_def':
  \<open>a \<prec> b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>c. a #\<^sub>J c \<and> a +\<^sub>J c = b)\<close>
  using less_sepadd_def positivity by auto

sublocale resource_ordering: ordering \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  apply standard
   apply (metis less_sepadd_def' less_eq_sepadd_def)
  apply (metis less_eq_sepadd_def positivity)
  done

sublocale resource_order: order \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  by standard (metis resource_ordering.antisym)

text \<open> Set up the isabelle machinery to treat this like an order. \<close>

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}, le = @{term \<open>(\<preceq>)\<close>}, lt = @{term \<open>(\<prec>)\<close>}},
    thms = {trans = @{thm resource_preordering.trans},
            refl = @{thm resource_preordering.refl},
            eqD1 = @{thm eq_refl}, eqD2 = @{thm eq_refl[OF sym]},
            antisym = @{thm resource_ordering.antisym}, contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF resource_order.less_le]},
                 nless_le = @{thm eq_reflection[OF resource_order.nless_le]}}
  }
\<close>

lemma le_res_less_le_not_le:
  \<open>a \<prec> b \<longleftrightarrow> a \<lesssim> b \<and> \<not> b \<lesssim> a\<close>
  by (metis part_of_def less_sepadd_def positivity)


subsubsection \<open> Unit Laws \<close>

text \<open> sepadd_unit is antimono \<close>
lemma below_unit_impl_unit:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_unit b \<Longrightarrow> sepadd_unit a\<close>
  unfolding sepadd_unit_def less_eq_sepadd_def part_of_def
  by (metis disjoint_add_rightL positivity)

lemma units_separate_to_units:
  \<open>x #\<^sub>J y \<Longrightarrow> sepadd_unit (x +\<^sub>J y) \<Longrightarrow> sepadd_unit x\<close>
  using below_unit_impl_unit partial_le_plus by blast

lemma le_unit_iff_eq:
  \<open>sepadd_unit b \<Longrightarrow> a \<preceq> b \<longleftrightarrow> b = a\<close>
  by (metis disjoint_preservation2 partial_le_plus resource_ordering.eq_iff sepadd_unit_def)

lemma units_least: \<open>sepadd_unit x \<Longrightarrow> x #\<^sub>J y \<Longrightarrow> x \<preceq> y\<close>
  by (metis partial_le_plus sepadd_unit_def)

lemma add_sepadd_unit_add_iff_parts_sepadd_unit[simp]:
  \<open>x #\<^sub>J y \<Longrightarrow> sepadd_unit (x +\<^sub>J y) \<longleftrightarrow> sepadd_unit x \<and> sepadd_unit y\<close>
  by (metis sepadd_unit_def units_separate_to_units)

lemma sepadd_unit_disjoint_trans:
  \<open>sepadd_unit a \<Longrightarrow> a #\<^sub>J b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  using disjoint_preservation units_least by blast

lemma positivity_alt:
  \<open>x #\<^sub>J u \<Longrightarrow> x +\<^sub>J u #\<^sub>J w \<Longrightarrow> x +\<^sub>J u +\<^sub>J w = x \<Longrightarrow> u +\<^sub>J x = x\<close>
  using positivity[of x u \<open>x +\<^sub>J u\<close> w]
  by (simp add: partial_add_commute)

lemma unit_sub_closure2:
  \<open>a #\<^sub>J x \<Longrightarrow> a +\<^sub>J x #\<^sub>J y \<Longrightarrow> a +\<^sub>J (x +\<^sub>J y) = a \<Longrightarrow> a +\<^sub>J x = a\<close>
  by (simp add: positivity partial_add_assoc2)

lemma unit_sub_closure2':
  \<open>a #\<^sub>J x \<Longrightarrow> a +\<^sub>J x #\<^sub>J y \<Longrightarrow> a +\<^sub>J x +\<^sub>J y = a \<Longrightarrow> a +\<^sub>J x = a\<close>
  by (simp add: positivity partial_add_assoc2)

lemma sepadd_punit_of_unit_antimono:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_punit_of b x \<Longrightarrow> sepadd_punit_of a x\<close>
  by (metis disjoint_preservation partial_le_plus2 resource_order.dual_order.eq_iff
      sepadd_punit_of_def sepadd_right_mono)

end


subsection \<open> Multi-unit Separation Algebra \<close>

class unitof =
  fixes unitof :: \<open>'a \<Rightarrow> 'a\<close>

class pre_multiunit_sep_alg = pre_perm_alg +\<^sub>J unitof +
  assumes unitof_disjoint[simp]: \<open>unitof a #\<^sub>J a\<close>
  assumes unitof_is_unit[simp]: \<open>\<And>a b. unitof a #\<^sub>J b \<Longrightarrow> unitof a +\<^sub>J b = b\<close>
begin

lemma le_iff_sepadd: \<open>a \<preceq> b \<longleftrightarrow> (\<exists>c. a #\<^sub>J c \<and> b = a +\<^sub>J c)\<close>
  by (metis disjoint_sym less_eq_sepadd_def partial_add_commute unitof_disjoint unitof_is_unit)

lemma le_iff_part_of: \<open>a \<preceq> b \<longleftrightarrow> a \<lesssim> b\<close>
  unfolding le_iff_sepadd part_of_def
  by blast

lemma unitof_disjoint2[simp,intro!]: \<open>a #\<^sub>J unitof a\<close>
  by (simp add: disjoint_sym)

lemma unitof_inherits_disjointness: \<open>a #\<^sub>J b \<Longrightarrow> unitof a #\<^sub>J b\<close>
  by (metis disjoint_add_leftL unitof_disjoint unitof_is_unit)

lemma unitof_is_unit2[simp]: \<open>b #\<^sub>J unitof a \<Longrightarrow> unitof a +\<^sub>J b = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_is_unitR[simp]: \<open>unitof a #\<^sub>J b \<Longrightarrow> b +\<^sub>J unitof a = b\<close>
  using partial_add_commute unitof_is_unit by presburger

lemma unitof_is_unitR2[simp]: \<open>b #\<^sub>J unitof a \<Longrightarrow> b +\<^sub>J unitof a = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_is_sepadd_unit: \<open>sepadd_unit (unitof a)\<close>
  by fastforce

lemma unitof_idem[simp]: \<open>unitof (unitof a) = unitof a\<close>
  by (metis unitof_disjoint unitof_is_unit unitof_is_unitR2)

lemma unitof_res_order_mono:
  \<open>a \<preceq> b \<Longrightarrow> unitof a \<preceq> unitof b\<close>
  by (metis disjoint_preservation related_units_identical
      resource_preorder.le_disj_eq_absorb unitof_disjoint2 unitof_is_sepadd_unit)


subsubsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma unitof_le[simp]: \<open>unitof x \<preceq> x\<close>
  using partial_le_plus unitof_disjoint
  by fastforce

lemma not_less_unitof[simp]: \<open>\<not> x \<prec> unitof x\<close>
  by (simp add: resource_preordering.strict_iff_not)

lemma disjoint_same_unit:
  \<open>a #\<^sub>J b \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

lemma common_disjoint_same_unit:
  \<open>a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

end

class multiunit_sep_alg = pre_multiunit_sep_alg +\<^sub>J perm_alg
begin

lemma le_unitof_then_eq[simp]: \<open>x \<preceq> unitof x \<Longrightarrow> x = unitof x\<close>
  using less_eq_sepadd_def positivity
  by fastforce

lemma le_unitof_eq[simp]: \<open>x \<preceq> unitof x \<longleftrightarrow> x = unitof x\<close>
  using le_unitof_then_eq
  by force

lemma unitof_less_iff_neq_unitof: \<open>unitof x \<prec> x \<longleftrightarrow> x \<noteq> unitof x\<close>
  by (simp add: resource_preorder.less_le_not_le)

lemma gr_unitofI: "(x = unitof x \<Longrightarrow> False) \<Longrightarrow> unitof x \<prec> x"
  using unitof_less_iff_neq_unitof by blast

lemma not_gr_unitof[simp]: "\<not> unitof x \<prec> x \<longleftrightarrow> x = unitof x"
  by (simp add: unitof_less_iff_neq_unitof)

lemma gr_implies_not_unitof: "z \<prec> x \<Longrightarrow> x \<noteq> unitof x"
  by (metis disjoint_add_rightL less_sepadd_def sepadd_unitE unitof_is_sepadd_unit)

lemma unitof_sepadd_unit:
  \<open>sepadd_unit x \<Longrightarrow> unitof x = x\<close>
  by (metis sepadd_unit_def unitof_disjoint2 unitof_is_unitR2)

lemma sepadd_eq_unitof_iff_both_eq_unitof[simp]:
  \<open>x #\<^sub>J y \<Longrightarrow> x +\<^sub>J y = unitof (x +\<^sub>J y) \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis (full_types) le_unitof_eq disjoint_add_swap_rl2 partial_le_plus unitof_is_unit
      unitof_inherits_disjointness unitof_is_unitR2)

lemma unitof_eq_sepadd_iff_both_eq_unitof[simp]:
  \<open>x #\<^sub>J y \<Longrightarrow> unitof (x +\<^sub>J y) = x +\<^sub>J y \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis sepadd_eq_unitof_iff_both_eq_unitof)

lemmas unitof_order = unitof_le le_unitof_eq not_less_unitof unitof_less_iff_neq_unitof not_gr_unitof

end


subsection \<open> (Single Unit) Separation Algebra\<close>

class pre_sep_alg = pre_multiunit_sep_alg +\<^sub>J zero +
  assumes zero_disjoint[simp]: \<open>0 #\<^sub>J a\<close>
  assumes zero_unit[simp]: \<open>0 +\<^sub>J a = a\<close>
begin

lemma zero_disjointR[simp]: \<open>a #\<^sub>J 0\<close>
  by (simp add: disjoint_sym)

lemma zero_unitR[simp]: \<open>a +\<^sub>J 0 = a\<close>
  using partial_add_commute zero_disjoint zero_unit
  by presburger

lemma zero_least: \<open>0 \<preceq> b\<close>
  using less_eq_sepadd_def
  by simp

lemma not_less_zero:
  "\<not> a \<prec> 0"
  using less_sepadd_def by auto

lemma zero_only_unit[simp]:
  \<open>sepadd_unit x \<longleftrightarrow> x = 0\<close>
  by (metis partial_add_commute sepadd_unit_def_strong zero_disjointR zero_unitR)

lemma unitof_eq_zero[simp]: \<open>unitof x = 0\<close>
  using unitof_is_sepadd_unit by auto

end

class sep_alg = pre_sep_alg +\<^sub>J perm_alg
begin

sublocale order_bot \<open>0\<close> \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  by standard
    (metis zero_least)


lemma gr_implies_not_zero: \<open>m \<prec> n \<Longrightarrow> n \<noteq> 0\<close>
  using not_less_zero by auto

subsubsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemmas le_zero = le_bot
lemmas zero_unique = bot_unique
lemmas zero_less = bot_less
lemmas zero_less_iff_neq_zero = sym[OF zero_less]

lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 \<prec> n"
  using zero_less_iff_neq_zero by auto

lemma not_gr_zero[simp]: "\<not> 0 \<prec> n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

lemma sepadd_eq_0_iff_both_eq_0[simp]:
  \<open>x #\<^sub>J y \<Longrightarrow> x +\<^sub>J y = 0 \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  by (metis less_sepadd_def zero_less_iff_neq_zero zero_unit)

lemma zero_eq_sepadd_iff_both_eq_0[simp]:
  \<open>x #\<^sub>J y \<Longrightarrow> 0 = x +\<^sub>J y \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  using sepadd_eq_0_iff_both_eq_0 by fastforce

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero

end


subsection \<open> Duplicable closure \<close>

class dupcl_perm_alg = perm_alg +
  assumes dup_sub_closure:
    \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = c \<Longrightarrow> c #\<^sub>J c \<Longrightarrow> c +\<^sub>J c = c \<Longrightarrow> a +\<^sub>J a = a\<close>
begin


text \<open>
  Duplicable sub-closure ensures that all elements less than a duplicable element
  are also duplicable.
\<close>

lemma dupp_sub_closureR: \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = c \<Longrightarrow> c #\<^sub>J c \<Longrightarrow> c +\<^sub>J c = c \<Longrightarrow> b +\<^sub>J b = b\<close>
  using disjoint_sym partial_add_commute dup_sub_closure by blast

text \<open> another form of dup_sub_closure \<close>
lemma sepadd_dup_antimono:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup a\<close>
  apply (clarsimp simp add: sepadd_dup_def)
  apply (rule conjI)
   apply (force dest: common_subresource_selfsep)
  apply (metis less_eq_sepadd_def dup_sub_closure)
  done

lemma sepadd_dup_plus_dupL:
  \<open>a #\<^sub>J b \<Longrightarrow> sepadd_dup (a +\<^sub>J b) \<Longrightarrow> sepadd_dup a\<close>
  using partial_le_plus sepadd_dup_antimono by auto

lemma sepadd_dup_plus_dupR:
  \<open>a #\<^sub>J b \<Longrightarrow> sepadd_dup (a +\<^sub>J b) \<Longrightarrow> sepadd_dup b\<close>
  using partial_le_plus2 sepadd_dup_antimono by auto

end


subsection \<open> Compatibility \<close>

context pre_perm_alg
begin

definition compatible :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>compatible \<equiv> ((\<preceq>) \<squnion> (\<succeq>))\<^sup>*\<^sup>*\<close>

lemmas compatible_induct[consumes 1] =
  rtranclp_induct[of \<open>(\<preceq>) \<squnion> (\<succeq>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas converse_compatible_induct[consumes 1] =
  converse_rtranclp_induct[of \<open>(\<preceq>) \<squnion> (\<succeq>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas compatibleE =
  rtranclE[of \<open>(\<preceq>) \<squnion> (\<succeq>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas converse_compatibleE =
  converse_rtranclpE[of \<open>(\<preceq>) \<squnion> (\<succeq>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas compatible_trans[trans] =
  rtranclp_trans[of \<open>(\<preceq>) \<squnion> (\<succeq>)\<close>, simplified compatible_def[symmetric], simplified]

lemma compatible_refl[intro!, simp]:
  \<open>compatible a a\<close>
  by (simp add: compatible_def)

lemma compatible_sym:
  assumes \<open>compatible a b\<close>
  shows \<open>compatible b a\<close>
proof -
  have \<open>((\<preceq>) \<squnion> (\<succeq>))\<^sup>*\<^sup>* = (((\<preceq>) \<squnion> (\<succeq>))\<inverse>\<inverse>)\<^sup>*\<^sup>*\<close>
    by (force intro!: arg_cong[of _ _ rtranclp])
  also have \<open>... = ((\<preceq>) \<squnion> (\<succeq>))\<^sup>*\<^sup>*\<inverse>\<inverse>\<close>
    by (simp add: rtranclp_conversep)
  finally show ?thesis
    by (metis assms compatible_def conversep_iff)
qed

lemma le_is_compatible[intro]:
  \<open>a \<preceq> b \<Longrightarrow> compatible a b\<close>
  by (simp add: compatible_def r_into_rtranclp)

lemma ge_is_compatible[intro]:
  \<open>a \<succeq> b \<Longrightarrow> compatible a b\<close>
  by (simp add: compatible_def r_into_rtranclp)

lemma trans_le_le_is_compatible[intro]:
  \<open>a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> compatible a c\<close>
  using le_is_compatible
  by (meson compatible_trans)

lemma trans_ge_ge_is_compatible[intro]:
  \<open>b \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> compatible a c\<close>
  using ge_is_compatible
  by (meson compatible_trans)

lemma trans_ge_le_is_compatible[intro]:
  \<open>b \<preceq> a \<Longrightarrow> b \<preceq> c \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

lemma trans_le_ge_is_compatible[intro]:
  \<open>a \<preceq> b \<Longrightarrow> c \<preceq> b \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

subsubsection \<open> Relation to other relations \<close>

lemma disjoint_rtrancl_implies_compatible:
  \<open>(#\<^sub>J)\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  apply (induct rule: rtranclp_induct)
   apply force
  apply (metis compatible_trans partial_le_plus partial_le_plus2 trans_le_ge_is_compatible)
  done

lemma implies_compatible_then_rtranscl_implies_compatible:
  \<open>\<forall>x y. r x y \<longrightarrow> compatible x y \<Longrightarrow> r\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  using implies_rel_then_rtranscl_implies_rel[of r _ _ compatible]
    compatible_trans
  by blast

lemma implies_compatible_then_rtranscl_implies_compatible2:
  \<open>r \<le> compatible \<Longrightarrow> r\<^sup>*\<^sup>* \<le> compatible\<close>
  using implies_compatible_then_rtranscl_implies_compatible
  by (simp add: le_fun_def)

subsubsection \<open> Relation to units \<close>

lemma step_compatible_units_identical:
  \<open>compatible b z \<Longrightarrow> a \<preceq> b \<or> b \<preceq> a \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  apply (induct rule: converse_compatible_induct)
   apply (metis disjoint_preservation2 disjoint_units_identical sepadd_unit_selfsep)
  apply (simp add: le_unit_iff_eq)
  apply (metis disjoint_preservation2 less_eq_sepadd_def sepadd_punit_of_unit_res_mono'
      sepadd_unit_def_strong)
  done

lemma compatible_units_identical:
  \<open>compatible a z \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  by (metis converse_compatibleE step_compatible_units_identical)

lemma compatible_unit_disjoint[dest]:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a #\<^sub>J u\<close>
  apply (induct rule: compatible_induct)
   apply force
  apply (metis disjoint_add_leftL disjoint_add_left_commute2 less_eq_sepadd_def sepadd_unit_right)
  done

lemma compatible_unit_disjoint2[dest]:
  \<open>compatible a u \<Longrightarrow> sepadd_unit u \<Longrightarrow> a #\<^sub>J u\<close>
  apply (induct rule: converse_compatible_induct)
   apply force
  apply (metis disjoint_add_leftL disjoint_add_left_commute2 less_eq_sepadd_def sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_left:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> u +\<^sub>J a = a\<close>
  apply (induct rule: compatible_induct)
   apply force
  apply (simp add: less_eq_sepadd_def)
  apply (elim disjE; clarsimp) (* 1 \<rightarrow> 2 *)
   apply (metis compatible_unit_disjoint disjoint_sym partial_add_assoc2)
  apply (metis compatible_unit_disjoint disjoint_add_leftL partial_add_commute sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_right:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a +\<^sub>J u = a\<close>
  by (simp add: compatible_unit_disjoint sepadd_unit_right)

end

context perm_alg
begin

lemma compatible_eq_strict_compatible:
  \<open>(compatible :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = ((\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
proof -
  have \<open>compatible = ((=) \<squnion> (\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
    unfolding compatible_def
    apply (rule arg_cong[of _ _ rtranclp])
    apply (simp add: less_sepadd_def less_eq_sepadd_def fun_eq_iff)
    apply (metis positivity)
    done
  also have \<open>... = ((\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
    by (metis inf_sup_aci(5) rtranclp_reflclp rtranclp_sup_rtranclp)
  finally show ?thesis .
qed

end

context pre_multiunit_sep_alg
begin

lemma same_unit_compatible:
  \<open>unitof a = unitof b \<Longrightarrow> compatible a b\<close>
  by (metis unitof_le trans_ge_le_is_compatible)

lemma compatible_then_same_unit:
  \<open>compatible a b \<Longrightarrow> unitof a = unitof b\<close>
  by (meson compatible_trans compatible_unit_disjoint2 ge_is_compatible common_disjoint_same_unit
      unitof_is_sepadd_unit unitof_le)

end


subsubsection \<open> All-compatible Resource Algebras \<close>

(* almost a sep_alg, in that if there was a unit, it would be a sep-algebra *)
class allcompatible_perm_alg = pre_perm_alg +
  assumes all_compatible: \<open>compatible a b\<close>
begin

lemma all_units_eq:
  \<open>sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (simp add: all_compatible compatible_units_identical)

end

(* allcompatible multiunit sep algebra collapses to a sep algebra *)
class allcompatible_sep_alg = allcompatible_perm_alg +\<^sub>J multiunit_sep_alg
begin

lemma exactly_one_unit: \<open>\<exists>!u. sepadd_unit u\<close>
  using all_compatible compatible_units_identical unitof_is_sepadd_unit by blast

definition \<open>the_unit \<equiv> The sepadd_unit\<close>

lemma the_unit_is_a_unit:
  \<open>sepadd_unit the_unit\<close>
  unfolding the_unit_def
  by (rule theI', simp add: exactly_one_unit)

sublocale is_sep_alg: sep_alg \<open>(+)\<close> \<open>(#\<^sub>J)\<close> the_unit \<open>(\<lambda>_. the_unit)\<close>
  apply standard
    apply (metis exactly_one_unit unitof_disjoint unitof_is_sepadd_unit the_unit_is_a_unit)
   apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit2 unitof_is_sepadd_unit
      the_unit_is_a_unit)
  apply (simp add: all_compatible compatible_unit_disjoint disjoint_sym_iff
      units_least the_unit_is_a_unit compatible_to_unit_is_unit_left; fail)
  done

end

context sep_alg
begin

subclass allcompatible_perm_alg
  by standard
    (simp add: same_unit_compatible)
thm same_unit_compatible

end


subsection \<open> Strongly Separated Separation Algebra \<close>

class strong_sep_pre_perm_alg = pre_perm_alg +
  assumes selfsep_implies_unit: \<open>a #\<^sub>J a \<Longrightarrow> sepadd_unit a\<close>
begin

lemma selfsep_iff:
  \<open>a #\<^sub>J a \<longleftrightarrow> sepadd_unit a\<close>
  using selfsep_implies_unit sepadd_unit_def by blast

lemma disjoint_implies_punit_iff_unit:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b \<longleftrightarrow> sepadd_unit a\<close>
  using selfsep_implies_unit
  by (simp add: sepadd_unit_def, metis disjoint_add_rightL)

end

class strong_sep_pre_multiunit_sep_alg = pre_multiunit_sep_alg +\<^sub>J strong_sep_pre_perm_alg
begin

lemma mu_selfsep_iff: \<open>a #\<^sub>J a \<longleftrightarrow> unitof a = a\<close>
  by (metis disjoint_units_identical selfsep_implies_unit unitof_disjoint2
      unitof_is_sepadd_unit)

lemma mu_selfsep_implies_unit: \<open>a #\<^sub>J a \<Longrightarrow> unitof a = a\<close>
  by (metis mu_selfsep_iff)

end

class strong_separated_pre_sep_alg = pre_sep_alg +\<^sub>J strong_sep_pre_multiunit_sep_alg
begin

lemma sepalg_selfsep_iff: \<open>a #\<^sub>J a \<longleftrightarrow> a = 0\<close>
  by (simp add: selfsep_iff)

lemma sepalg_selfsep_implies_unit: \<open>a #\<^sub>J a \<Longrightarrow> a = 0\<close>
  by (metis sepalg_selfsep_iff)

end


subsection \<open> Disjoint Parts Algebra \<close>

class disjoint_parts_pre_perm_alg = pre_perm_alg +
  assumes disjointness_left_plusI: \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a +\<^sub>J b #\<^sub>J c\<close>
begin

lemmas disjointness_left_plusI' =
  disjointness_left_plusI
  disjointness_left_plusI[OF disjoint_sym]
  disjointness_left_plusI[OF _ disjoint_sym]
  disjointness_left_plusI[OF _ _ disjoint_sym]
  disjointness_left_plusI[OF _ disjoint_sym disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym _ disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym disjoint_sym disjoint_sym]

lemma disjointness_right_plusI:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c\<close>
  using disjointness_left_plusI disjoint_sym by auto

lemmas disjointness_right_plusI' =
  disjointness_right_plusI
  disjointness_right_plusI[OF disjoint_sym]
  disjointness_right_plusI[OF _ disjoint_sym]
  disjointness_right_plusI[OF _ _ disjoint_sym]
  disjointness_right_plusI[OF _ disjoint_sym disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym _ disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym disjoint_sym disjoint_sym]

lemma disjointness_left_plus_eq[simp]:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b #\<^sub>J c \<longleftrightarrow> a #\<^sub>J c \<and> b #\<^sub>J c\<close>
  by (metis disjointness_left_plusI disjoint_add_leftL disjoint_add_leftR)

lemma disjointness_right_plus_eq[simp]:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<longleftrightarrow> a #\<^sub>J b \<and> a #\<^sub>J c\<close>
  by (metis disjointness_right_plusI disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_double_assoc2:
  \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> a #\<^sub>J d \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> b #\<^sub>J d \<Longrightarrow> c #\<^sub>J d \<Longrightarrow> a +\<^sub>J b +\<^sub>J (c +\<^sub>J d) = (a +\<^sub>J c) +\<^sub>J (b +\<^sub>J d)\<close>
  by (meson disjointness_right_plusI partial_add_double_assoc)

end


subsection \<open> Trivial Self-disjointness Separation Algebra \<close>

class trivial_selfdisjoint_pre_perm_alg = pre_perm_alg +
  assumes selfdisjoint_same: \<open>a #\<^sub>J a \<Longrightarrow> a +\<^sub>J a = b \<Longrightarrow> a = b\<close>
begin

text \<open> All selfdisjoint elements are duplicable \<close>

lemma all_selfdisjoint_dup:
  \<open>a #\<^sub>J a \<Longrightarrow> sepadd_dup a\<close>
  using selfdisjoint_same sepadd_dup_def by presburger

end

context strong_sep_pre_perm_alg
begin
(* trivial selfdisjointness is a subclass of strong separation *)
subclass trivial_selfdisjoint_pre_perm_alg
  by standard (simp add: selfsep_iff)

end


subsection \<open> Cross-Split Separation Algebra \<close>

class crosssplit_pre_perm_alg = pre_perm_alg +
  assumes cross_split:
  \<open>a #\<^sub>J b \<Longrightarrow> c #\<^sub>J d \<Longrightarrow> a +\<^sub>J b = c +\<^sub>J d \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac #\<^sub>J ad \<and> bc #\<^sub>J bd \<and> ac #\<^sub>J bc \<and> ad #\<^sub>J bd \<and>
      ac +\<^sub>J ad = a \<and> bc +\<^sub>J bd = b \<and> ac +\<^sub>J bc = c \<and> ad +\<^sub>J bd = d\<close>


subsection \<open> Cancellative Separation Algebras\<close>

class cancel_pre_perm_alg = pre_perm_alg +
  assumes partial_right_cancel[simp]: \<open>\<And>a b c. a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> (a +\<^sub>J c = b +\<^sub>J c) = (a = b)\<close>
begin

lemma partial_right_cancel2[simp]:
  \<open>c #\<^sub>J a \<Longrightarrow> c #\<^sub>J b \<Longrightarrow> (a +\<^sub>J c = b +\<^sub>J c) = (a = b)\<close>
  using partial_right_cancel disjoint_sym
  by force

lemma partial_left_cancel[simp]:
  \<open>a #\<^sub>J c \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> (c +\<^sub>J a = c +\<^sub>J b) = (a = b)\<close>
  by (metis partial_add_commute partial_right_cancel)

lemma partial_left_cancel2[simp]:
  \<open>c #\<^sub>J a \<Longrightarrow> c #\<^sub>J b \<Longrightarrow> (c +\<^sub>J a = c +\<^sub>J b) = (a = b)\<close>
  using partial_left_cancel disjoint_sym
  by force

lemmas partial_right_cancelD = iffD1[OF partial_right_cancel, rotated 2]
lemmas partial_right_cancel2D = iffD1[OF partial_right_cancel2, rotated 2]
lemmas partial_left_cancelD = iffD1[OF partial_left_cancel, rotated 2]
lemmas partial_left_cancel2D = iffD1[OF partial_left_cancel2, rotated 2]

lemma cancel_right_to_unit:
  assumes
    \<open>a #\<^sub>J b\<close>
    \<open>a +\<^sub>J b = b\<close>
  shows \<open>sepadd_unit a\<close>
  unfolding sepadd_unit_def_strong
proof (intro conjI allI impI)
  show Daa: \<open>a #\<^sub>J a\<close>
    using assms
    by (metis disjoint_add_rightL)

  fix c
  assume D0:
    \<open>a #\<^sub>J c\<close>

  have E1: \<open>a = a +\<^sub>J a\<close>
  proof -
    have \<open>b #\<^sub>J a +\<^sub>J a\<close>
      using assms
      by (simp add: disjoint_add_swap_rl disjoint_sym)
    moreover have \<open>b +\<^sub>J a = b +\<^sub>J (a +\<^sub>J a)\<close>
      using assms
      by (metis partial_add_assoc3 partial_add_commute disjoint_add_swap_rl disjoint_sym)
    ultimately show ?thesis
      using assms
      by (simp add: disjoint_sym_iff)
  qed

  have D1: \<open>c +\<^sub>J a #\<^sub>J a\<close>
    using assms D0 E1 Daa
    by (metis disjoint_add_left_commute)

  have \<open>a +\<^sub>J c = a +\<^sub>J (c +\<^sub>J a)\<close>
    using assms D0 E1 Daa
    by (metis partial_add_assoc partial_add_commute)
  then show \<open>a +\<^sub>J c = c\<close>
    using D0 D1
    by (metis partial_left_cancelD disjoint_sym partial_add_commute)
qed

lemma cancel_left_to_unit:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = a \<Longrightarrow> sepadd_unit b\<close>
  by (metis cancel_right_to_unit disjoint_sym partial_add_commute)

end

class cancel_pre_multiunit_sep_alg = cancel_pre_perm_alg +\<^sub>J pre_multiunit_sep_alg
begin

lemma selfsep_selfadd_iff_unit:
  \<open>a #\<^sub>J a \<and> a +\<^sub>J a = a \<longleftrightarrow> sepadd_unit a\<close>
  using cancel_left_to_unit by blast

end

class cancel_multiunit_sep_alg = cancel_pre_perm_alg +\<^sub>J multiunit_sep_alg
begin

lemma strong_positivity:
  \<open>a #\<^sub>J b \<Longrightarrow> c #\<^sub>J c \<Longrightarrow> a +\<^sub>J b = c \<Longrightarrow> c +\<^sub>J c = c \<Longrightarrow> a = b \<and> b = c\<close>
  by (metis add_sepadd_unit_add_iff_parts_sepadd_unit cancel_right_to_unit disjoint_units_identical
      sepadd_unit_right)

end

class cancel_pre_sep_alg = cancel_pre_multiunit_sep_alg +\<^sub>J pre_sep_alg


subsection \<open> No-unit perm alg \<close>

text \<open>
  Here we create a perm_alg without any unit.
  Such an algebra is necessary to prove permission heaps are cancellative.
\<close>
class no_unit_pre_perm_alg = pre_perm_alg +
  assumes no_units: \<open>\<And>a. \<not> sepadd_unit a\<close>

class cancel_no_unit_pre_perm_alg = no_unit_pre_perm_alg +\<^sub>J cancel_pre_perm_alg
begin

lemma no_unit_cancel_rightD[dest]:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b \<Longrightarrow> False\<close>
  using cancel_right_to_unit no_units by blast

lemma no_unit_cancel_leftD[dest]:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = a \<Longrightarrow> False\<close>
  using cancel_left_to_unit no_units by blast

end


subsection \<open> Halving separation algebra \<close>

class halfof =
  fixes halfof :: \<open>'a \<Rightarrow> 'a\<close>

class halving_pre_perm_alg = pre_perm_alg +\<^sub>J halfof +
  assumes halfof_additive_split: \<open>\<And>a. halfof a +\<^sub>J halfof a = a\<close>
  assumes halfof_self_disjoint: \<open>\<And>a. halfof a #\<^sub>J halfof a\<close>
  assumes halfof_sepadd_distrib: \<open>\<And>a b. a #\<^sub>J b \<Longrightarrow> halfof (a +\<^sub>J b) = halfof a +\<^sub>J halfof b\<close>
begin

lemma halfof_disjoint_preservation_left: \<open>a #\<^sub>J b \<Longrightarrow> halfof a #\<^sub>J b\<close>
  by (metis disjoint_add_leftR halfof_additive_split halfof_self_disjoint)

lemma halfof_disjoint_preservation_right: \<open>a #\<^sub>J b \<Longrightarrow> a #\<^sub>J halfof b\<close>
  using halfof_disjoint_preservation_left disjoint_sym by blast

lemma halfof_disjoint_preservation: \<open>a #\<^sub>J b \<Longrightarrow> halfof a #\<^sub>J halfof b\<close>
  by (simp add: halfof_disjoint_preservation_left halfof_disjoint_preservation_right)


lemma halfof_disjoint_distribL:
  \<open>a #\<^sub>J c \<Longrightarrow> a +\<^sub>J c #\<^sub>J b \<Longrightarrow> a +\<^sub>J halfof c #\<^sub>J b +\<^sub>J halfof c\<close>
  by (metis disjoint_add_leftL disjoint_add_right_commute disjoint_sym halfof_additive_split
      halfof_self_disjoint partial_add_assoc)

lemma halfof_disjoint_distribR:
  \<open>b #\<^sub>J c \<Longrightarrow> a #\<^sub>J b +\<^sub>J c \<Longrightarrow> a +\<^sub>J halfof c #\<^sub>J b +\<^sub>J halfof c\<close>
  using halfof_disjoint_distribL disjoint_sym by blast

lemma halfof_eq_full_imp_self_additive:
  \<open>halfof a = a \<Longrightarrow> a +\<^sub>J a = a\<close>
  by (metis halfof_additive_split)

end


subsubsection \<open> Trivial self-disjoint +\<^sub>J halving (very boring) \<close>

class trivial_halving_perm_alg = trivial_selfdisjoint_pre_perm_alg +\<^sub>J halving_pre_perm_alg
begin

lemma trivial_halfof[simp]: \<open>halfof a = a\<close>
  by (simp add: selfdisjoint_same halfof_additive_split halfof_self_disjoint)

lemma all_duplicable:
  \<open>sepadd_dup x\<close>
  using all_selfdisjoint_dup halfof_self_disjoint
  by auto

end


subsection \<open> All-disjoint algebra \<close>

text \<open>
  This is a ver strong condition. The discrete algebra is this sort of algebra.
  This law is sufficient to make a destructive error state work.
\<close>

class all_disjoint_pre_perm_alg = pre_perm_alg +
  assumes all_disjoint[simp]: \<open>a #\<^sub>J b\<close>

class all_disjoint_pre_multiunit_sep_alg =
  pre_multiunit_sep_alg +\<^sub>J all_disjoint_pre_perm_alg

class all_disjoint_pre_sep_alg =
  pre_sep_alg +\<^sub>J all_disjoint_pre_perm_alg


context perm_alg
begin

lemma noncancellative_res_implies_all_below_disjoint:
  \<open>R = {(a,b,a+b)|a b::'a. a #\<^sub>J b} \<Longrightarrow>
    AB = (\<lambda>c. {(a,b)|a b::'a. a #\<^sub>J c \<and> b #\<^sub>J c \<and> a +\<^sub>J c = b +\<^sub>J c \<and> a \<noteq> b}) \<Longrightarrow>
    (a,b) \<in> AB c \<Longrightarrow> \<not> a #\<^sub>J b\<close>
  nitpick[card 'a=2]
  sorry

end
*)

section \<open> Logic \<close>

context join_alg
begin

subsection \<open> Connectives \<close>

paragraph  \<open> Sepconj \<close>

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<close> 88) where
  \<open>P \<^emph> Q \<equiv> \<lambda>c. \<exists>a b. \<^bold>J a b c \<and> P a \<and> Q b\<close>

lemma sepconj_apply: \<open>(P \<^emph> Q) c = (\<exists>a b. \<^bold>J a b c \<and> P a \<and> Q b)\<close>
  by (simp add: sepconj_def)

lemma sepconjI: \<open>\<^bold>J a b c \<Longrightarrow> P a \<Longrightarrow> Q b \<Longrightarrow> (P \<^emph> Q) c\<close>
  using sepconj_apply by auto

lemma sepconj_commI: \<open>\<^bold>J b a c \<Longrightarrow> P a \<Longrightarrow> Q b \<Longrightarrow> (P \<^emph> Q) c\<close>
  using sepconj_apply join_comm
  by metis

lemma sepconjE[elim]:
  \<open>(P \<^emph> Q) c \<Longrightarrow> (\<And>a b. \<^bold>J a b c \<Longrightarrow> P a \<Longrightarrow> Q b \<Longrightarrow> R) \<Longrightarrow> R\<close>
  using sepconj_apply by auto


paragraph \<open> Sepimp \<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 64) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>a. \<forall>b c. \<^bold>J a b c \<longrightarrow> P b \<longrightarrow> Q c\<close>


paragraph \<open> Septract \<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 64) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>a. \<exists>b c. \<^bold>J a b c \<and> P b \<and> Q c\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 64) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>a. \<exists>b c. \<^bold>J a b c \<and> Q b \<and> P c\<close>

paragraph \<open> Sepcoimp \<close>

text \<open> See Bannister et. al. [BHK2018] for more discussion of this connective. \<close>
definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 64) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>c. \<forall>a b. \<^bold>J a b c \<longrightarrow> P a \<longrightarrow> Q b\<close>


abbreviation(input) emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> is_join_unit\<close>


paragraph \<open> Iterated Sepconj \<close>

fun iter_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iter_sepconj (P # Ps) = P \<^emph> iter_sepconj Ps\<close>
| \<open>iter_sepconj [] = emp\<close>

end

context join_functional
begin

lemma sepconj_as_plus_def:
  \<open>(P \<^emph> Q) = (\<lambda>c. \<exists>a b. a #\<^sub>J b \<and> c = a +\<^sub>J b \<and> P a \<and> Q b)\<close>
  by (simp add: sepconj_def disjoint_join_def, metis join_then_plus_join_eq)

lemma sepconj_iff_plus:
  \<open>(P \<^emph> Q) c \<longleftrightarrow> (\<exists>a b. a #\<^sub>J b \<and> c = a +\<^sub>J b \<and> P a \<and> Q b)\<close>
  by (simp add: sepconj_as_plus_def)

lemma sepconj_directI[intro]: \<open>h1 #\<^sub>J h2 \<Longrightarrow> P h1 \<Longrightarrow> Q h2 \<Longrightarrow> (P \<^emph> Q) (h1 +\<^sub>J h2)\<close>
  by (metis sepconj_iff_plus)

lemma sepconj_crossI[intro]: \<open>h1 #\<^sub>J h2 \<Longrightarrow> P h1 \<Longrightarrow> Q h2 \<Longrightarrow> (P \<^emph> Q) (h2 +\<^sub>J h1)\<close>
  by (metis sepconj_iff_plus plus_join_commute)

lemma sepconj_plusE:
  \<open>(P \<^emph> Q) r \<Longrightarrow> (\<And>h1 h2. h1 #\<^sub>J h2 \<Longrightarrow> r = h1 +\<^sub>J h2 \<Longrightarrow> P h1 \<Longrightarrow> Q h2 \<Longrightarrow> Z) \<Longrightarrow> Z\<close>
  using sepconj_iff_plus by auto

end


subsection \<open> Laws \<close>

context join_alg
begin

paragraph \<open> Sepconj \<close>

lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  unfolding sepconj_def fun_eq_iff
  by (meson join_assoc join_comm)

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def fun_eq_iff
  by (meson join_comm)

lemma sepconj_left_comm: \<open>Q \<^emph> (P \<^emph> R) = P \<^emph> (Q \<^emph> R)\<close>
  unfolding sepconj_def fun_eq_iff
  by (meson join_assoc join_comm)

lemmas sepconj_ac = sepconj_assoc sepconj_comm sepconj_left_comm

lemma sepconj_mono[intro]:
  \<open>P \<le> P' \<Longrightarrow> Q \<le> Q' \<Longrightarrow> P \<^emph> Q \<le> P' \<^emph> Q'\<close>
  using sepconj_def by auto

lemma sepconj_monoL[intro]:
  \<open>P \<le> Q \<Longrightarrow> P \<^emph> R \<le> Q \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_monoR[intro]:
  \<open>Q \<le> R \<Longrightarrow> P \<^emph> Q \<le> P \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_middle_monotone_lhsR: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> D\<close>
  by (metis (no_types, lifting) sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_lhsL: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> D \<^emph> B\<close>
  by (metis (no_types, lifting) sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsR: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> D \<^emph> B2\<close>
  by (metis (no_types, lifting) sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsL: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> D \<^emph> B2\<close>
  by (metis (no_types, lifting) sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_lhsR2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> C\<close>
  by (simp add: sepconj_middle_monotone_lhsR)

lemma sepconj_middle_monotone_lhsL2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (simp add: sepconj_middle_monotone_lhsL)

lemma sepconj_middle_monotone_rhsR2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsR)

lemma sepconj_middle_monotone_rhsL2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsL)

\<comment> \<open> An important law from quantale theory. \<close>
lemma sepconj_Sup_distrib:
  \<open>p \<^emph> \<Squnion>P = \<Squnion>((\<^emph>) p ` P)\<close>
  by (simp add: fun_eq_iff sepconj_def Bex_def, blast)

lemma sepconj_Sup_distrib2:
  \<open>\<Squnion>P \<^emph> p  = \<Squnion>{p' \<^emph> p|p'. p' \<in> P}\<close>
  using sepconj_comm
  by (simp add: sepconj_Sup_distrib, blast)


paragraph \<open> Sepimp\<close>

lemma sepimp_sepconjL:
  \<open>P \<^emph> Q \<midarrow>\<^emph> R = P \<midarrow>\<^emph> Q \<midarrow>\<^emph> R\<close>
  by (simp add: sepconj_def sepimp_def fun_eq_iff)
    (meson join_assoc join_comm)

lemma sepimp_conjR:
  \<open>P \<midarrow>\<^emph> Q \<sqinter> R = (P \<midarrow>\<^emph> Q) \<sqinter> (P \<midarrow>\<^emph> R)\<close>
  by (force simp add: sepimp_def fun_eq_iff)

lemma sepimp_top_eq[simp]:
  \<open>P \<midarrow>\<^emph> \<top> = \<top>\<close>
  by (simp add: sepimp_def fun_eq_iff)


paragraph \<open> septract \<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)


paragraph \<open> sepcoimp \<close>

lemma sepcoimp_sepconjL: \<open>P \<^emph> Q \<sim>\<^emph> R = P \<sim>\<^emph> Q \<sim>\<^emph> R\<close>
  by (simp add: sepcoimp_def sepconj_def fun_eq_iff)
    (meson join_assoc join_comm)

paragraph  \<open> emp \<close>

lemma weak_emp_sepconj_weak: \<open>\<top> \<le> emp \<midarrow>\<odot> p \<Longrightarrow> p \<le> emp \<^emph> p\<close>
  apply (clarsimp simp add: septract_def sepconj_def le_fun_def)
  apply (meson is_join_unit_def join_comm)
  done

lemma weak_emp_sepconj: \<open>\<top> \<le> emp \<midarrow>\<odot> p \<Longrightarrow> join_order_mono p \<Longrightarrow> emp \<^emph> p = p\<close>
  by (metis (mono_tags, lifting) join_order_mono_def sepconjE order_antisym_conv predicate1I
      weak_emp_sepconj_weak)


paragraph \<open> Duality \<close>

lemma septract_sepimp_dual: \<open>P \<midarrow>\<odot> Q = -(P \<midarrow>\<^emph> (-Q))\<close>
  unfolding septract_def sepimp_def
  by force

lemma sepimp_sepcoimp_dual: \<open>P \<sim>\<^emph> Q = -(P \<^emph> (-Q))\<close>
  unfolding sepconj_def sepcoimp_def
  by force

lemma sepcoimp_sepimp_dual: \<open>P \<^emph> Q = -(P \<sim>\<^emph> -Q)\<close>
  unfolding sepconj_def sepcoimp_def
  by force

lemma sepconj_sepimp_galois: \<open>P \<^emph> Q \<le> R \<longleftrightarrow> P \<le> Q \<midarrow>\<^emph> R\<close>
  using sepconj_def sepimp_def by fastforce

lemma sepcoimp_septract_galois: \<open>P \<odot>\<midarrow> Q \<le> R \<longleftrightarrow> P \<le> Q \<sim>\<^emph> R\<close>
  unfolding sepcoimp_def septract_rev_def le_fun_def
  using join_comm by fastforce

end

context join_functional
begin

lemma sepconj_eqpred_eq:
  \<open>((=) a \<^emph> (=) b) = (\<lambda>x. a #\<^sub>J b \<and> x = a +\<^sub>J b)\<close>
  using sepconj_plusE by blast

lemma sepconj_eqpred_combine[simp]:
  \<open>a #\<^sub>J b \<Longrightarrow> ((=) a \<^emph> (=) b) = ((=) (a +\<^sub>J b))\<close>
  by (force simp add: sepconj_eqpred_eq fun_eq_iff)

end

context join_positive
begin

lemma weak_emp_sepconj2: \<open>emp \<midarrow>\<odot> p \<le> \<bottom> \<Longrightarrow> join_order_mono p \<Longrightarrow> emp \<^emph> p = \<bottom>\<close>
  sledgehammer
  sorry

end


context join_munital
begin

lemma emp_unit_weak:
  \<open>p \<le> emp \<^emph> p\<close>
  apply (clarsimp simp add: sepconj_def is_join_unit_def fun_eq_iff)
  apply (metis is_join_unit_def join_unitof_unital unitof_is_join_unit)
  done

lemma emp_unit:
  \<open>join_order_mono p \<Longrightarrow> emp \<^emph> p = p\<close>
  apply (clarsimp simp add: sepconj_def is_join_unit_def fun_eq_iff)
  apply (metis is_join_unit_def join_unitof_unital unitof_is_join_unit join_order_mono_def)
  done

end


section \<open> Bibliography \<close>

text \<open>
  [KKB2012] Gerwin Klein, Rafal Kolanski, and Andrew Boyton. 2012.
      "Mechanised Separation Algebra." ITP 2012.
      \<^url>\<open>https://doi.org/10.1007/978-3-642-32347-8_22\<close>.

  [VSTBook2014] Andrew W. Appel, Robert Dockins, Aquinas Hobor, Lennart Beringer, Josiah Dodds,
      Gordon Stewart, Sandrine Blazy, and Xavier Leroy.
      2014. "Chapter 6 - Separation Algebras."
      In Program Logics for Certified Compilers, 1st ed. Cambridge University Press.
      \<^url>\<open>https://doi.org/10.1017/CBO9781107256552\<close>.

  [BHK2018] Callum Bannister, Peter Höfner, and Gerwin Klein.
      2018. "Backwards and Forwards with Separation Logic." ITP 2018.
      \<^url>\<open>https://doi.org/10.1007/978-3-319-94821-8_5\<close>.

  TODO:
  Brotherstone & Villard
\<close>

end