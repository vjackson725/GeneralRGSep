theory SepLogic
  imports Util
begin

text \<open>
  This file implements a hierarchy of typeclasses for resource algebras.
  This is inspired by Klein et. al's [KKB2012] Isabelle/HOL separation algebra typeclasses
  and Appel et. al.'s [VSTBook2014] typeclass hierarchy in Coq.
\<close>

section \<open> Common Notions \<close>

class disjoint =
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>##\<close> 60)

section \<open> Permission Algebras \<close>

class perm_alg = disjoint + plus +
  (* partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  assumes disjoint_sym: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  (* separation laws *)
  assumes positivity:
    \<open>a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b\<close>
begin

lemma trans_helper:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> \<exists>d. a ## d \<and> a + b + c = a + d\<close>
  by (metis disjoint_add_rightL disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)

lemma disjoint_sym_iff: \<open>a ## b \<longleftrightarrow> b ## a\<close>
  using disjoint_sym by blast

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_sym by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_sym partial_add_commute)

lemma disjoint_add_right_commute2:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> c ## b + a\<close>
  by (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma disjoint_add_left_commute:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> c + b ## a\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute)

lemma disjoint_add_left_commute2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a + c ## b\<close>
  by (metis disjoint_add_leftR disjoint_add_left_commute partial_add_commute)

lemma disjoint_add_swap_rl:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute partial_add_commute)

lemma disjoint_add_swap_rl2:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + c ## b\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute partial_add_commute)

lemma disjoint_add_swap_lr:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## b + c\<close>
  by (simp add: disjoint_add_right_commute2 disjoint_sym_iff partial_add_commute)

lemma disjoint_add_swap_lr2:
  \<open>a ## c \<Longrightarrow> a + c ## b \<Longrightarrow> a ## b + c\<close>
  by (metis disjoint_add_left_commute disjoint_sym_iff)

lemma disjoint_middle_swap:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a + b + c ## d \<Longrightarrow> a + c ## b + d\<close>
  by (metis disjoint_add_leftR disjoint_add_right_commute2 disjoint_add_swap_lr disjoint_sym_iff
      partial_add_assoc)

lemma disjoint_middle_swap2:
  \<open>b ## c \<Longrightarrow> b + c ## d \<Longrightarrow> a ## b + c + d \<Longrightarrow> a + c ## b + d\<close>
  by (metis disjoint_add_rightR disjoint_add_right_commute2 disjoint_add_rightL partial_add_assoc
      partial_add_commute)

lemma partial_add_left_commute:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis partial_add_assoc partial_add_commute disjoint_sym)

lemma partial_add_left_commute2:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis partial_add_left_commute disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_right_commute:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + b + c = a + c + b\<close>
  by (simp add: disjoint_sym partial_add_assoc partial_add_commute)

lemma partial_add_assoc_commute_left:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> b + a + c = a + (b + c)\<close>
  by (metis partial_add_assoc partial_add_commute)

lemma partial_add_assoc_commute_right:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c + b = a + (b + c)\<close>
  by (metis partial_add_commute partial_add_assoc_commute_left partial_add_right_commute)

lemma partial_add_assoc2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  using disjoint_add_leftL disjoint_add_leftR partial_add_assoc by blast

lemma partial_add_assoc3:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  by (meson disjoint_add_rightR disjoint_add_rightL partial_add_assoc)

lemma partial_add_double_assoc:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> b ## c + d \<Longrightarrow> a ## b + (c + d) \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute partial_add_assoc
      partial_add_left_commute)

subsection \<open> order \<close>

text \<open>
  Resources give rise to a natural order, but it's not the same as standard
  order implementations unless all elements have a unit.
\<close>

text \<open>
  The 'part_of' relation is almost an order, except that it doesn't satisfy reflexivity.
\<close>

definition (in perm_alg) part_of :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<lesssim>\<close> 50) where
  \<open>a \<lesssim> b \<equiv> \<exists>c. a ## c \<and> a + c = b\<close>

lemma part_of_trans[trans]:
  \<open>a \<lesssim> b \<Longrightarrow> b \<lesssim> c \<Longrightarrow> a \<lesssim> c\<close>
  by (fastforce dest: trans_helper simp add: part_of_def)

text \<open> This lemma is just positivity stated another way. \<close>
lemma part_of_antisym:
  \<open>a \<lesssim> b \<Longrightarrow> b \<lesssim> a \<Longrightarrow> a = b\<close>
  using part_of_def positivity by auto

definition less_eq_sepadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<close> 50) where
  \<open>(\<preceq>) \<equiv> \<lambda>a b. a = b \<or> a \<lesssim> b\<close>

lemmas less_eq_sepadd_def' = less_eq_sepadd_def[simplified part_of_def]

definition less_sepadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<close> 50) where
  \<open>(\<prec>) \<equiv> \<lambda>a b. a \<noteq> b \<and> a \<lesssim> b\<close>

lemmas less_sepadd_def' = less_sepadd_def[simplified part_of_def]

abbreviation (input) greater_eq_sepadd  (infix \<open>\<succeq>\<close> 50)
  where \<open>(\<succeq>) \<equiv> \<lambda>x y. (\<preceq>) y x\<close>

abbreviation (input) greater_sepadd (infix \<open>\<succ>\<close> 50)
  where \<open>(\<succ>) \<equiv> \<lambda>x y. (\<prec>) y x\<close>


sublocale resource_ordering: ordering \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  apply standard
     apply (metis less_eq_sepadd_def)
    apply (metis less_eq_sepadd_def part_of_trans)
   apply (force dest: part_of_antisym simp add: less_sepadd_def less_eq_sepadd_def)
  apply (metis less_eq_sepadd_def part_of_antisym)
  done

sublocale resource_order: order \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  apply standard
     apply (force dest: part_of_antisym simp add: less_sepadd_def less_eq_sepadd_def)
    apply (metis resource_ordering.refl)
   apply (metis resource_ordering.trans)
  apply (metis resource_ordering.antisym)
  done

text \<open> Set up the isabelle machinery to treat this like an order. \<close>

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}, le = @{term \<open>(\<preceq>)\<close>}, lt = @{term \<open>(\<prec>)\<close>}},
    thms = {trans = @{thm resource_ordering.trans},
            refl = @{thm resource_ordering.refl},
            eqD1 = @{thm eq_refl}, eqD2 = @{thm eq_refl[OF sym]},
            antisym = @{thm resource_ordering.antisym}, contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF resource_order.less_le]},
                 nless_le = @{thm eq_reflection[OF resource_order.nless_le]}}
  }
\<close>

lemma le_res_less_le_not_le:
  \<open>a \<prec> b \<longleftrightarrow> a \<lesssim> b \<and> \<not> b \<lesssim> a\<close>
  by (metis part_of_def less_sepadd_def positivity)

lemma partial_le_plus: \<open>a ## b \<Longrightarrow> a \<preceq> a + b\<close>
  by (meson less_eq_sepadd_def part_of_def)

lemma partial_le_plus2: \<open>a ## b \<Longrightarrow> b \<preceq> a + b\<close>
  by (metis partial_le_plus disjoint_sym partial_add_commute)

lemma partial_le_part_left: \<open>a ## b \<Longrightarrow> a + b \<preceq> c \<Longrightarrow> a \<preceq> c\<close>
  using resource_ordering.trans partial_le_plus by blast

lemma partial_le_part_right: \<open>a ## b \<Longrightarrow> a + b \<preceq> c \<Longrightarrow> b \<preceq> c\<close>
  using resource_ordering.trans partial_le_plus2 by blast

lemma common_subresource_selfsep:
  \<open>a ## b \<Longrightarrow> ab \<preceq> a \<Longrightarrow> ab \<preceq> b \<Longrightarrow> ab ## ab\<close>
  by (metis disjoint_add_rightL disjoint_sym less_eq_sepadd_def part_of_def)

lemma selfdisjoint_over_selfdisjoint:
  \<open>a ## a \<Longrightarrow> \<forall>x. x \<preceq> a \<longrightarrow> x ## x\<close>
  using common_subresource_selfsep by blast

lemma disjoint_preservation:
  \<open>a' \<preceq> a \<Longrightarrow> a ## b \<Longrightarrow> a' ## b\<close>
  by (metis disjoint_add_rightL disjoint_sym less_eq_sepadd_def part_of_def)

lemma disjoint_preservation2:
  \<open>b' \<preceq> b \<Longrightarrow> a ## b \<Longrightarrow> a ## b'\<close>
  using disjoint_preservation disjoint_sym by blast

lemma sepadd_left_mono:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b \<preceq> c \<Longrightarrow> a + b \<preceq> a + c\<close>
  by (metis disjoint_add_swap_rl less_eq_sepadd_def part_of_def partial_add_assoc3)

lemma sepadd_right_mono: \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> a \<preceq> b \<Longrightarrow> a + c \<preceq> b + c\<close>
  by (metis disjoint_sym_iff partial_add_commute sepadd_left_mono)


subsection \<open> sepadd_unit \<close>

definition \<open>sepadd_unit a \<equiv> (\<exists>b. a ## b) \<and> (\<forall>b. a ## b \<longrightarrow> a + b = b)\<close>

lemma sepadd_unitI[intro]:
  \<open>a ## b \<Longrightarrow> (\<And>b. a ## b \<Longrightarrow> a + b = b) \<Longrightarrow> sepadd_unit a\<close>
  using sepadd_unit_def by blast

lemma sepadd_unitE[elim]:
  \<open>sepadd_unit a \<Longrightarrow> (\<And>b. a ## b \<Longrightarrow> (\<And>b. a ## b \<Longrightarrow> a + b = b) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using sepadd_unit_def by blast

lemma sepadd_unitD:
  \<open>sepadd_unit a \<Longrightarrow> \<exists>b. a ## b\<close>
  \<open>sepadd_unit a \<Longrightarrow> a ## b \<Longrightarrow> a + b = b\<close>
  by blast+

abbreviation \<open>sepadd_units \<equiv> Collect sepadd_unit\<close>

text \<open> sepadd_unit is antimono; positivity said a different way \<close>
lemma below_unit_impl_unit:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_unit b \<Longrightarrow> sepadd_unit a\<close>
  unfolding sepadd_unit_def less_eq_sepadd_def part_of_def
  by (metis disjoint_add_rightL positivity)

lemma units_separate_to_units:
  \<open>x ## y \<Longrightarrow> sepadd_unit (x + y) \<Longrightarrow> sepadd_unit x\<close>
  using below_unit_impl_unit partial_le_plus by blast

lemma le_unit_iff_eq:
  \<open>sepadd_unit b \<Longrightarrow> a \<preceq> b \<longleftrightarrow> b = a\<close>
  by (metis disjoint_preservation2 partial_le_plus resource_ordering.eq_iff sepadd_unit_def)

lemma units_least: \<open>sepadd_unit x \<Longrightarrow> x ## y \<Longrightarrow> x \<preceq> y\<close>
  by (metis partial_le_plus sepadd_unit_def)

lemma units_are_selfdisjoint:
  \<open>(\<forall>b. a ## b \<longrightarrow> a + b = b) \<Longrightarrow> a ## b \<Longrightarrow> a ## a\<close>
  by (metis disjoint_add_rightL)

lemma sepadd_unit_selfsep[dest]:
  \<open>sepadd_unit a \<Longrightarrow> a ## a\<close>
  using units_are_selfdisjoint sepadd_unit_def
  by blast

lemma sepadd_unit_def_strong:
  \<open>sepadd_unit a \<longleftrightarrow> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = b)\<close>
  by blast

lemma sepadd_unit_idem_add[simp]: \<open>sepadd_unit u \<Longrightarrow> u + u = u\<close>
  using sepadd_unit_def units_are_selfdisjoint by auto

lemmas sepadd_unit_left = sepadd_unitD(2)

lemma sepadd_unit_right: \<open>sepadd_unit u \<Longrightarrow> a ## u \<Longrightarrow> a + u = a\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_left)

lemma add_sepadd_unit_add_iff_parts_sepadd_unit[simp]:
  \<open>x ## y \<Longrightarrow> sepadd_unit (x + y) \<longleftrightarrow> sepadd_unit x \<and> sepadd_unit y\<close>
  by (metis sepadd_unit_def units_separate_to_units)

lemma disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_def)

lemma related_units_disjoint:
  \<open>sepadd_unit u1 \<Longrightarrow> sepadd_unit u2 \<Longrightarrow> a ## u1 \<Longrightarrow> a ## u2 \<Longrightarrow> u1 ## u2\<close>
  by (metis disjoint_add_leftL disjoint_sym sepadd_unit_def)

lemma related_units_identical:
  \<open>sepadd_unit u1 \<Longrightarrow> sepadd_unit u2 \<Longrightarrow> a ## u1 \<Longrightarrow> a ## u2 \<Longrightarrow> u2 = u1\<close>
  using related_units_disjoint disjoint_units_identical by blast

lemma trans_disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit c \<Longrightarrow> a = c\<close>
  by (metis disjoint_sym related_units_identical)

lemma sepadd_unit_disjoint_trans:
  \<open>sepadd_unit a \<Longrightarrow> a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_preservation units_least by blast

lemma unit_sub_closure2:
  \<open>a ## x \<Longrightarrow> a + x ## y \<Longrightarrow> a + (x + y) = a \<Longrightarrow> a + x = a\<close>
  by (simp add: positivity partial_add_assoc2)

lemma unit_sub_closure2':
  \<open>a ## x \<Longrightarrow> a + x ## y \<Longrightarrow> a + x + y = a \<Longrightarrow> a + x = a\<close>
  by (simp add: positivity partial_add_assoc2)


subsection \<open> Pseudo-units \<close>

text \<open> Pseudo-units: 'units' for certain resources. Can be non-unital for other resources. \<close>
definition (in perm_alg) \<open>sepadd_punit_of u x \<equiv> u ## x \<and> u + x = x\<close>

lemma wunit_is_punit: \<open>sepadd_unit u \<Longrightarrow> Ex (sepadd_punit_of u)\<close>
  using sepadd_punit_of_def sepadd_unit_def by blast

lemma sepadd_punit_of_unit_antimono:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_punit_of b x \<Longrightarrow> sepadd_punit_of a x\<close>
  by (metis disjoint_preservation partial_le_plus2 resource_order.dual_order.eq_iff
      sepadd_punit_of_def sepadd_right_mono)

lemma sepadd_punit_of_unit_res_mono:
  \<open>x \<preceq> y \<Longrightarrow> sepadd_punit_of a x \<Longrightarrow> sepadd_punit_of a y\<close>
  by (metis disjoint_add_swap_lr less_eq_sepadd_def' partial_add_assoc3 sepadd_punit_of_def)

lemma sepadd_punit_of_unit_res_mono':
  \<open>x \<preceq> y \<Longrightarrow> a ## x \<Longrightarrow> a + x = x \<Longrightarrow> a ## y \<and> a + y = y\<close>
  using sepadd_punit_of_unit_res_mono
  by (simp add: sepadd_punit_of_def)


subsection \<open> zero_sepadd \<close>

definition \<open>sepadd_zero a \<equiv> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = a)\<close>

text \<open> sepadd_zero is antimono \<close>
lemma above_zero_impl_zero:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_zero a \<Longrightarrow> sepadd_zero b\<close>
  by (metis less_eq_sepadd_def part_of_def sepadd_zero_def)

lemma zeros_add_to_zero: \<open>x ## y \<Longrightarrow> sepadd_zero x \<Longrightarrow> sepadd_zero (x + y)\<close>
  by (simp add: sepadd_zero_def)


subsection \<open> duplicable \<close>

lemma add_to_selfsep_preserves_selfsep: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> a ## a\<close>
  by (meson disjoint_add_rightL disjoint_sym)

lemma add_to_selfsep_preserves_selfsepR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> b ## b\<close>
  using disjoint_sym partial_add_commute add_to_selfsep_preserves_selfsep by blast

definition \<open>sepadd_dup a \<equiv> a ## a \<and> a + a = a\<close>

lemma units_are_dup: \<open>sepadd_unit a \<Longrightarrow> sepadd_dup a\<close>
  by (simp add: sepadd_unit_selfsep sepadd_dup_def)

lemma zeros_are_dup: \<open>sepadd_zero a \<Longrightarrow> sepadd_dup a\<close>
  by (simp add: sepadd_dup_def sepadd_zero_def)


subsection \<open>sepdomeq\<close>

definition \<open>sepdomeq a b \<equiv> \<forall>c. a ## c = b ## c\<close>

lemma sepdomeq_reflp:
  \<open>reflp sepdomeq\<close>
  by (simp add: reflpI sepdomeq_def)

lemma sepdomeq_symp:
  \<open>symp sepdomeq\<close>
  by (metis sepdomeq_def sympI)

lemma sepdomeq_transp:
  \<open>transp sepdomeq\<close>
  by (simp add: sepdomeq_def transp_def)

lemma same_sepdom_disjoint_leftD:
  \<open>sepdomeq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomeq_def)

lemma sepdomeq_disjoint_rightD:
  \<open>sepdomeq a b \<Longrightarrow> b ## c \<Longrightarrow> a ## c\<close>
  by (simp add: sepdomeq_def)

definition \<open>sepdomsubseteq a b \<equiv> \<forall>c. a ## c \<longrightarrow> b ## c\<close>

lemma sepdomsubseteq_reflp:
  \<open>reflp sepdomsubseteq\<close>
  by (simp add: reflpI sepdomsubseteq_def)

lemma sepdomsubseteq_transp:
  \<open>transp sepdomsubseteq\<close>
  by (simp add: sepdomsubseteq_def transp_def)

lemma sepdomsubseteq_disjointD:
  \<open>sepdomsubseteq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomsubseteq_def)


subsection \<open> Seplogic connectives \<close>

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<close> 88) where
  \<open>P \<^emph> Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

lemma sepconj_iff: \<open>(P \<^emph> Q) r = (\<exists>h1 h2. h1 ## h2 \<and> r = h1 + h2 \<and> P h1 \<and> Q h2)\<close>
  by (simp add: sepconj_def)

lemma sepconjI[intro]: \<open>h1 ## h2 \<Longrightarrow> r = h1 + h2 \<Longrightarrow> P h1 \<Longrightarrow> Q h2 \<Longrightarrow> (P \<^emph> Q) r\<close>
  using sepconj_iff by auto

lemma sepconjE[elim!]:
  \<open>(P \<^emph> Q) r \<Longrightarrow> (\<And>h1 h2. h1 ## h2 \<Longrightarrow> r = h1 + h2 \<Longrightarrow> P h1 \<Longrightarrow> Q h2 \<Longrightarrow> Z) \<Longrightarrow> Z\<close>
  using sepconj_iff by auto

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 65) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h ## h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

text \<open> See Bannister et. al. [BHK2018] for more discussion of this connective. \<close>
definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 65) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 ## h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 67) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h ## h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 67) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h ## h' \<and> P (h + h') \<and> Q h'\<close>

definition subheapexist :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>subheapexist P \<equiv> \<lambda>h. \<exists>h1. h1 \<preceq> h \<and> P h1\<close>

definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> \<lambda>x. sepadd_unit x\<close>

fun iter_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iter_sepconj (P # Ps) = P \<^emph> iter_sepconj Ps\<close>
| \<open>iter_sepconj [] = emp\<close>

subsection \<open> Seplogic connective properties \<close>

subsubsection \<open> Sepconj \<close>

lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (intro ext iffI)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def
  by (metis disjoint_sym partial_add_commute)

lemma sepconj_left_comm: \<open>Q \<^emph> (P \<^emph> R) = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (rule ext)
  apply (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute
      partial_add_left_commute)
  done

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

lemma sepconj_comm_imp:
  \<open>P \<^emph> Q \<le> Q \<^emph> P\<close>
  by (simp add: sepconj_comm)

lemma sepconj_middle_monotone_lhsR: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> D\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_lhsL: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> D \<^emph> B\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsR: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> D \<^emph> B2\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsL: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> D \<^emph> B2\<close>
  using sepconj_comm sepconj_middle_monotone_rhsR by presburger

lemma sepconj_middle_monotone_lhsR2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> C\<close>
  by (simp add: sepconj_middle_monotone_lhsR)

lemma sepconj_middle_monotone_lhsL2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (simp add: sepconj_middle_monotone_lhsL)

lemma sepconj_middle_monotone_rhsR2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsR)

lemma sepconj_middle_monotone_rhsL2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsL)

lemma sepconj_eq_eq:
  \<open>((=) h1 \<^emph> (=) h2) = (\<lambda>x. h1 ## h2 \<and> x = h1 + h2)\<close>
  by (simp add: sepconj_def fun_eq_iff)

lemma sepconj_eq_eq2:
  \<open>h1 ## h2 \<Longrightarrow> ((=) h1 \<^emph> (=) h2) = ((=) (h1 + h2))\<close>
  by (force simp add: sepconj_eq_eq)

subsubsection \<open> emp \<close>

lemma weak_emp_sepconj: \<open>\<top> \<le> emp \<midarrow>\<odot> p \<Longrightarrow> emp \<^emph> p = p\<close>
  by (simp add: emp_def sepadd_unit_def septract_def sepconj_def le_fun_def fun_eq_iff)
    (metis disjoint_sym_iff)

lemma weak_emp_sepconj2: \<open>emp \<midarrow>\<odot> p \<le> \<bottom> \<Longrightarrow> emp \<^emph> p = \<bottom>\<close>
  by (simp add: emp_def sepadd_unit_def septract_def sepconj_def le_fun_def fun_eq_iff)
    (metis disjoint_sym_iff partial_add_commute)

subsubsection \<open> Sepimp \<close>

lemma sepimp_sepconjL:
  \<open>P \<^emph> Q \<midarrow>\<^emph> R = P \<midarrow>\<^emph> Q \<midarrow>\<^emph> R\<close>
  apply (clarsimp simp add: sepconj_def sepimp_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

lemma sepimp_conjR:
  \<open>P \<midarrow>\<^emph> Q \<sqinter> R = (P \<midarrow>\<^emph> Q) \<sqinter> (P \<midarrow>\<^emph> R)\<close>
  by (force simp add: sepimp_def fun_eq_iff)

lemma sepimp_top_eq[simp]:
  \<open>P \<midarrow>\<^emph> \<top> = \<top>\<close>
  by (simp add: sepimp_def fun_eq_iff)


subsubsection \<open> everything else \<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)


(*

\<^emph>   < ~ >  \<midarrow>\<^emph>
|           X
\<sim>\<^emph>  < ~ > \<midarrow>\<odot>

*)


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
  using disjoint_sym partial_add_commute by fastforce

lemma sepcoimp_curry: \<open>P \<sim>\<^emph> Q \<sim>\<^emph> R = P \<^emph> Q \<sim>\<^emph> R\<close>
  apply (clarsimp simp add: sepcoimp_def sepconj_def)
  apply (intro ext iffI; clarsimp)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

subsection \<open> Precision \<close>

definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h h1 h2. h1 \<preceq> h \<longrightarrow> h2 \<preceq> h \<longrightarrow> P h1 \<longrightarrow> P h2 \<longrightarrow> h1 = h2\<close>

subsection \<open> sepconj/conj distributivity \<close>

text \<open> this direction is always true \<close>
lemma sepconj_conj_semidistrib:
  \<open>f \<^emph> (q1 \<sqinter> q2) \<le> (f \<^emph> q1) \<sqinter> (f \<^emph> q2)\<close>
  by (force simp add: le_fun_def)

text \<open>
  The following predicates are equivalent to precision in a cancellative algebra,
  but incomparable in a more generic setting.
\<close>

definition sepconj_conj_distrib :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>sepconj_conj_distrib P \<equiv> (\<forall>Q Q'. (P \<^emph> Q) \<sqinter> (P \<^emph> Q') \<le> P \<^emph> (Q \<sqinter> Q'))\<close>

lemma sepconj_conj_distribD:
  \<open>sepconj_conj_distrib P \<Longrightarrow> P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  unfolding sepconj_conj_distrib_def
  by (meson antisym sepconj_conj_semidistrib)

lemma sepconj_conj_distrib_then_sepconj_imp_sepcoimp:
  \<open>sepconj_conj_distrib P \<Longrightarrow> P \<^emph> Q \<le> P \<sim>\<^emph> Q\<close>
  unfolding sepconj_conj_distrib_def sepconj_def sepcoimp_def fun_eq_iff le_fun_def
  apply clarsimp
  apply (rename_tac h1 h1' h2 h2')
  apply (drule_tac x=\<open>(=) h1'\<close> in spec, drule_tac x=\<open>(=) h2'\<close> in spec)
  apply blast
  done

lemma sepconj_imp_sepcoimp_then_sepconj_conj_distrib:
  \<open>(\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q) \<Longrightarrow> sepconj_conj_distrib P\<close>
  unfolding sepconj_conj_distrib_def sepconj_def sepcoimp_def fun_eq_iff le_fun_def
  apply (clarsimp simp add: imp_ex_conjL imp_conjL)
  apply (rename_tac h1 h1' h2 h2')
  apply (drule_tac x=\<open>(=) h1'\<close> in spec)
  apply blast
  done

lemma sepconj_conj_distrib_iff_sepconj_imp_sepcoimp:
  \<open>sepconj_conj_distrib P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  using sepconj_conj_distrib_then_sepconj_imp_sepcoimp
    sepconj_imp_sepcoimp_then_sepconj_conj_distrib
  by blast

lemma sepconj_imp_sepcoimp_iff_sepconj_eq_strong_sepcoimp:
  \<open>(\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def fun_eq_iff)
  apply (intro iffI allI conjI impI)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  done

lemma sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp:
  \<open>sepconj_conj_distrib P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  by (meson sepconj_conj_distrib_iff_sepconj_imp_sepcoimp
      sepconj_imp_sepcoimp_iff_sepconj_eq_strong_sepcoimp)

lemmas sepconj_conj_distrib_then_sepconj_eq_strong_sepcoimp =
  iffD1[OF sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp]

lemmas sepconj_eq_strong_sepcoimp_then_sepconj_conj_distrib =
  iffD2[OF sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp]

lemma eqpred_sepconj_conj_distrib_impl_cancel:
  \<open>sepconj_conj_distrib ((=) c) \<Longrightarrow>
    a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c = b + c \<Longrightarrow> a = b\<close>
  apply (clarsimp simp add: sepconj_conj_distrib_def sepconj_def le_fun_def)
  apply (drule_tac x=\<open>(=) a\<close> and y=\<open>(=) b\<close> in spec2)
  apply (simp add: disjoint_sym_iff partial_add_commute)
  done

lemma sepconj_conj_distrib_impl_septract_sepconj_imp:
  \<open>sepconj_conj_distrib P \<Longrightarrow> (P \<midarrow>\<odot> P \<^emph> Q) \<le> Q\<close>
  by (simp add: sepcoimp_septract_galois sepconj_conj_distrib_then_sepconj_imp_sepcoimp septract_reverse)

lemma septract_sepconj_imp_impl_sepconj_conj_distrib:
  \<open>\<forall>Q. (P \<midarrow>\<odot> P \<^emph> Q) \<le> Q \<Longrightarrow> sepconj_conj_distrib P\<close>
  by (simp add: sepcoimp_septract_galois sepconj_conj_distrib_iff_sepconj_imp_sepcoimp
      septract_reverse)
  

subsection \<open> Intuitionistic \<close>

(* TODO: rename intuitionistic to bring it in line with the seplogic jungle paper *)
definition intuitionistic :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>intuitionistic P \<equiv> \<forall>h h'. h \<preceq> h' \<longrightarrow> P h \<longrightarrow> P h'\<close>

lemma precise_to_intuitionistic:
  \<open>precise P \<Longrightarrow> intuitionistic (P \<^emph> \<top>)\<close>
  unfolding sepconj_def precise_def intuitionistic_def
  by (metis less_eq_sepadd_def' partial_le_part_left resource_ordering.antisym top_conj(1))

lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def)

lemma sepconj_pdisj_distrib_left: \<open>P \<^emph> (Q1 \<squnion> Q2) = P \<^emph> Q1 \<squnion> P \<^emph> Q2\<close>
  by (force simp add: sepconj_def)

lemma sepcoimp_pconj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<sqinter> Q') = (P \<sim>\<^emph> Q) \<sqinter> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: sepcoimp_def)

subsection \<open> Supported \<close>

definition supported :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>supported P \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>hp. P hp \<and> hp \<preceq> s \<and> (\<forall>s'. hp \<preceq> s' \<longrightarrow> s' \<preceq> s \<longrightarrow> P s'))\<close>

lemma precise_to_supported:
  \<open>precise P \<Longrightarrow> supported (P \<^emph> \<top>)\<close>
  using resource_ordering.eq_iff supported_def by auto

end


section \<open> Multi-unit Separation Algebra \<close>

class multiunit_sep_alg = perm_alg +
  fixes unitof :: \<open>'a \<Rightarrow> 'a\<close>
  assumes unitof_disjoint[simp]: \<open>unitof a ## a\<close>
  assumes unitof_is_unit[simp]: \<open>\<And>a b. unitof a ## b \<Longrightarrow> unitof a + b = b\<close>
begin

lemma le_iff_sepadd: \<open>a \<preceq> b \<longleftrightarrow> (\<exists>c. a ## c \<and> b = a + c)\<close>
  by (metis disjoint_sym less_eq_sepadd_def' partial_add_commute unitof_disjoint unitof_is_unit)

lemma le_iff_part_of: \<open>a \<preceq> b \<longleftrightarrow> a \<lesssim> b\<close>
  unfolding part_of_def le_iff_sepadd
  by blast

lemma unitof_disjoint2[simp,intro!]: \<open>a ## unitof a\<close>
  by (simp add: disjoint_sym)

lemma unitof_inherits_disjointness: \<open>a ## b \<Longrightarrow> unitof a ## b\<close>
  by (metis disjoint_add_leftL unitof_disjoint unitof_is_unit)

lemma unitof_is_unit2[simp]: \<open>b ## unitof a \<Longrightarrow> unitof a + b = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_is_unitR[simp]: \<open>unitof a ## b \<Longrightarrow> b + unitof a = b\<close>
  using partial_add_commute unitof_is_unit by presburger

lemma unitof_is_unitR2[simp]: \<open>b ## unitof a \<Longrightarrow> b + unitof a = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_idem[simp]: \<open>unitof (unitof a) = unitof a\<close>
  by (metis unitof_disjoint unitof_is_unit unitof_is_unitR2)

lemma unitof_is_sepadd_unit: \<open>sepadd_unit (unitof a)\<close>
  by fastforce


subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma unitof_le[simp]: \<open>unitof x \<preceq> x\<close>
  using partial_le_plus unitof_disjoint
  by fastforce

lemma le_unitof_eq[simp]: \<open>x \<preceq> unitof x \<longleftrightarrow> x = unitof x\<close>
  by (auto intro: resource_ordering.antisym)

lemma not_less_unitof[simp]: \<open>\<not> x \<prec> unitof x\<close>
  by (simp add: resource_order.leD)

lemma unitof_less_iff_neq_unitof: \<open>unitof x \<prec> x \<longleftrightarrow> x \<noteq> unitof x\<close>
  by (metis resource_order.antisym_conv2 unitof_le)

lemma gr_unitofI: "(x = unitof x \<Longrightarrow> False) \<Longrightarrow> unitof x \<prec> x"
  using unitof_less_iff_neq_unitof by blast

lemma not_gr_unitof[simp]: "\<not> unitof x \<prec> x \<longleftrightarrow> x = unitof x"
  by (simp add: unitof_less_iff_neq_unitof)

lemma gr_implies_not_unitof: "z \<prec> x \<Longrightarrow> x \<noteq> unitof x"
  by (metis le_unit_iff_eq resource_order.dual_order.strict_iff_not unitof_is_sepadd_unit)

lemma unitof_sepadd_unit:
  \<open>sepadd_unit x \<Longrightarrow> unitof x = x\<close>
  by (metis sepadd_unit_def unitof_disjoint2 unitof_is_unitR2)

lemma sepadd_eq_unitof_iff_both_eq_unitof[simp]:
  \<open>x ## y \<Longrightarrow> x + y = unitof (x + y) \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis add_sepadd_unit_add_iff_parts_sepadd_unit unitof_is_sepadd_unit unitof_sepadd_unit)

lemma unitof_eq_sepadd_iff_both_eq_unitof[simp]:
  \<open>x ## y \<Longrightarrow> unitof (x + y) = x + y \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis sepadd_eq_unitof_iff_both_eq_unitof)

lemma disjoint_same_unit:
  \<open>a ## b \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

lemma common_disjoint_same_unit:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

lemmas unitof_order = unitof_le le_unitof_eq not_less_unitof unitof_less_iff_neq_unitof not_gr_unitof


subsection \<open> emp \<close>

text \<open> emp is not really useful until now, where every element has a unit. \<close>

lemma emp_sepconj_unit[simp]: \<open>emp \<^emph> P = P\<close>
  apply (simp add: emp_def sepconj_def fun_eq_iff)
  apply (metis sepadd_unit_left unitof_disjoint unitof_is_sepadd_unit)
  done

lemma emp_sepconj_unit_right[simp]: \<open>P \<^emph> emp = P\<close>
  using emp_sepconj_unit sepconj_comm by force

lemma secoimp_imp_sepconj:
  \<open>P \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<sqinter> emp)\<close>
  apply (simp add: sepcoimp_def sepconj_def le_fun_def emp_def)
  apply (metis unitof_disjoint2 unitof_is_unitR2 unitof_is_sepadd_unit)
  done

lemma not_coimp_emp:
  \<open>\<not> sepadd_unit h \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
  by (simp add: sepcoimp_def emp_def sepadd_unit_def,
      metis unitof_disjoint unitof_is_unit)

lemma supported_intuitionistic_to_precise:
  \<open>supported P \<Longrightarrow> intuitionistic P \<Longrightarrow> precise (P \<sqinter> - (P \<^emph> (-emp)))\<close>
  nitpick[card=4]
  oops

end


section \<open> (Single Unit) Separation Algebra\<close>

class sep_alg = multiunit_sep_alg + zero +
  assumes zero_disjoint[simp]: \<open>0 ## a\<close>
  assumes zero_unit[simp]: \<open>0 + a = a\<close>
begin

lemma zero_disjointR[simp]: \<open>a ## 0\<close>
  by (simp add: disjoint_sym)

lemma zero_unitR[simp]: \<open>a + 0 = a\<close>
  using partial_add_commute zero_disjoint zero_unit
  by presburger

lemma zero_least[iff]: \<open>0 \<preceq> b\<close>
  using less_eq_sepadd_def'
  by simp

sublocale order_bot \<open>0\<close> \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  by standard
    (metis zero_least)

lemma unitof_eq_zero[simp]: \<open>unitof x = 0\<close>
  by (metis common_disjoint_same_unit disjoint_preservation le_unitof_eq unitof_disjoint
      unitof_is_sepadd_unit unitof_sepadd_unit zero_least)

lemma zero_only_unit[simp]:
  \<open>sepadd_unit x \<longleftrightarrow> x = 0\<close>
  by (metis unitof_is_sepadd_unit unitof_sepadd_unit unitof_eq_zero)

subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma zero_less_iff_neq_zero: "0 \<prec> n \<longleftrightarrow> n \<noteq> 0"
  using bot_less by auto

lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 \<prec> n"
  using zero_less_iff_neq_zero by auto

lemma not_gr_zero[simp]: "\<not> 0 \<prec> n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

lemma gr_implies_not_zero: \<open>m \<prec> n \<Longrightarrow> n \<noteq> 0\<close>
  using not_less_bot by auto

lemma sepadd_eq_0_iff_both_eq_0[simp]: \<open>x ## y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  using sepadd_eq_unitof_iff_both_eq_unitof by auto

lemma zero_eq_sepadd_iff_both_eq_0[simp]: \<open>x ## y \<Longrightarrow> 0 = x + y \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  using sepadd_eq_0_iff_both_eq_0 by fastforce

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero


paragraph \<open> Separation Logic \<close>

lemma emp_apply:
  \<open>emp x \<longleftrightarrow> x = 0\<close>
  by (simp add: emp_def)

lemma not_coimp_emp0:
  \<open>h \<noteq> 0 \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

end


section \<open> Duplicable closure \<close>

class dupcl_perm_alg = perm_alg +
  assumes dup_sub_closure:
    \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a + a = a\<close>
begin


text \<open>
  Duplicable sub-closure ensures that all elements less than a duplicable element
  are also duplicable.
\<close>

lemma dupp_sub_closureR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> b + b = b\<close>
  using disjoint_sym partial_add_commute dup_sub_closure by blast

text \<open> another form of dup_sub_closure \<close>
lemma sepadd_dup_antimono:
  \<open>a \<preceq> b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup a\<close>
  apply (clarsimp simp add: sepadd_dup_def)
  apply (rule conjI)
   apply (force dest: common_subresource_selfsep)
  apply (metis less_eq_sepadd_def part_of_def dup_sub_closure)
  done

lemma sepadd_dup_plus_dupL:
  \<open>a ## b \<Longrightarrow> sepadd_dup (a + b) \<Longrightarrow> sepadd_dup a\<close>
  using partial_le_plus sepadd_dup_antimono by auto

lemma sepadd_dup_plus_dupR:
  \<open>a ## b \<Longrightarrow> sepadd_dup (a + b) \<Longrightarrow> sepadd_dup b\<close>
  using partial_le_plus2 sepadd_dup_antimono by auto

end


section \<open> Compatibility \<close>

context perm_alg
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
  using le_is_compatible by force

lemma trans_ge_ge_is_compatible[intro]:
  \<open>b \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> compatible a c\<close>
  using ge_is_compatible by force

lemma trans_ge_le_is_compatible[intro]:
  \<open>b \<preceq> a \<Longrightarrow> b \<preceq> c \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

lemma trans_le_ge_is_compatible[intro]:
  \<open>a \<preceq> b \<Longrightarrow> c \<preceq> b \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

subsection \<open> Relation to other relations \<close>

lemma disjoint_rtrancl_implies_compatible:
  \<open>(##)\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  apply (induct rule: rtranclp_induct)
   apply force
  apply (metis compatible_trans partial_le_plus partial_le_plus2 trans_le_ge_is_compatible)
  done

lemma compatible_eq_strict_compatible:
  \<open>(compatible :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = ((\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
proof -
  have \<open>compatible = ((=) \<squnion> (\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
    by (force intro: arg_cong[of _ _ rtranclp]
        simp add: compatible_def less_sepadd_def less_eq_sepadd_def)
  also have \<open>... = ((\<prec>) \<squnion> (\<succ>))\<^sup>*\<^sup>*\<close>
    by (metis inf_sup_aci(5) rtranclp_reflclp rtranclp_sup_rtranclp)
  finally show ?thesis .
qed

lemma implies_compatible_then_rtranscl_implies_compatible:
  \<open>\<forall>x y. r x y \<longrightarrow> compatible x y \<Longrightarrow> r\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  using implies_rel_then_rtranscl_implies_rel[of r _ _ compatible]
    compatible_trans
  by blast

lemma implies_compatible_then_rtranscl_implies_compatible2:
  \<open>r \<le> compatible \<Longrightarrow> r\<^sup>*\<^sup>* \<le> compatible\<close>
  using implies_compatible_then_rtranscl_implies_compatible
  by (simp add: le_fun_def)


subsection \<open> Relation to units \<close>

lemma step_compatible_units_identical:
  \<open>compatible b z \<Longrightarrow> a \<preceq> b \<or> b \<preceq> a \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  apply (induct rule: converse_compatible_induct)
   apply (force simp add: le_unit_iff_eq)
  apply (simp add: le_unit_iff_eq)
  apply (metis disjoint_preservation2 le_unit_iff_eq less_eq_sepadd_def' sepadd_unit_left
      resource_ordering.trans)
  done

lemma compatible_units_identical:
  \<open>compatible a z \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  by (metis converse_compatibleE step_compatible_units_identical)

lemma compatible_unit_disjoint[dest]:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a ## u\<close>
  apply (induct rule: compatible_induct)
   apply force
  apply (metis disjoint_add_leftL disjoint_add_left_commute2 less_eq_sepadd_def' sepadd_unit_right)
  done

lemma compatible_unit_disjoint2[dest]:
  \<open>compatible a u \<Longrightarrow> sepadd_unit u \<Longrightarrow> a ## u\<close>
  apply (induct rule: converse_compatible_induct)
   apply force
  apply (metis disjoint_add_leftL disjoint_add_left_commute2 less_eq_sepadd_def' sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_left:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> u + a = a\<close>
  apply (induct rule: compatible_induct)
   apply force
  apply (simp add: less_eq_sepadd_def')
  apply (elim disjE; clarsimp) (* 1 \<rightarrow> 2 *)
   apply (metis compatible_unit_disjoint disjoint_sym partial_add_assoc2)
  apply (metis compatible_unit_disjoint disjoint_add_leftL partial_add_commute sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_right:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a + u = a\<close>
  by (simp add: compatible_unit_disjoint sepadd_unit_right)

end

context multiunit_sep_alg
begin

lemma same_unit_compatible:
  \<open>unitof a = unitof b \<Longrightarrow> compatible a b\<close>
  by (metis trans_ge_le_is_compatible unitof_le)

lemma compatible_then_same_unit:
  \<open>compatible a b \<Longrightarrow> unitof a = unitof b\<close>
  by (metis compatible_trans compatible_unit_disjoint2 disjoint_same_unit unitof_idem
      unitof_is_sepadd_unit same_unit_compatible)

end


subsection \<open> All-compatible Resource Algebras \<close>

(* almost a sep_alg, in that if there was a unit, it would be a sep-algebra *)
class allcompatible_perm_alg = perm_alg +
  assumes all_compatible: \<open>compatible a b\<close>
begin

lemma all_units_eq:
  \<open>sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (simp add: all_compatible compatible_units_identical)

end

(* allcompatible multiunit sep algebras collapse *)
class allcompatible_multiunit_sep_alg = allcompatible_perm_alg + multiunit_sep_alg
begin

lemma exactly_one_unit: \<open>\<exists>!u. sepadd_unit u\<close>
  using all_compatible compatible_units_identical unitof_is_sepadd_unit by blast

definition \<open>the_unit \<equiv> The sepadd_unit\<close>

lemma the_unit_is_a_unit:
  \<open>sepadd_unit the_unit\<close>
  unfolding the_unit_def
  by (rule theI', simp add: exactly_one_unit)

sublocale is_sep_alg: sep_alg the_unit \<open>(+)\<close> \<open>(##)\<close> \<open>(\<lambda>_. the_unit)\<close>
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

end


section \<open> Strongly Separated Separation Algebra \<close>

class strong_sep_perm_alg = perm_alg +
  assumes selfsep_implies_unit: \<open>a ## a \<Longrightarrow> sepadd_unit a\<close>
begin

lemma selfsep_iff:
  \<open>a ## a \<longleftrightarrow> sepadd_unit a\<close>
  using selfsep_implies_unit sepadd_unit_def by blast

end

class strong_sep_multiunit_sep_alg = multiunit_sep_alg + strong_sep_perm_alg
begin

lemma mu_selfsep_iff: \<open>a ## a \<longleftrightarrow> unitof a = a\<close>
  by (metis selfsep_iff unitof_disjoint unitof_sepadd_unit)

lemma mu_selfsep_implies_unit: \<open>a ## a \<Longrightarrow> unitof a = a\<close>
  by (metis mu_selfsep_iff)

end

class strong_separated_sep_alg = sep_alg + strong_sep_multiunit_sep_alg
begin

lemma sepalg_selfsep_iff: \<open>a ## a \<longleftrightarrow> a = 0\<close>
  by (simp add: selfsep_iff)

lemma sepalg_selfsep_implies_unit: \<open>a ## a \<Longrightarrow> a = 0\<close>
  by (metis sepalg_selfsep_iff)

end


section \<open> Disjoint Parts Algebra \<close>

class disjoint_parts_perm_alg = perm_alg +
  assumes disjointness_left_plusI: \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + b ## c\<close>
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
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a ## b + c\<close>
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
  \<open>a ## b \<Longrightarrow> a + b ## c \<longleftrightarrow> a ## c \<and> b ## c\<close>
  by (metis disjointness_left_plusI disjoint_add_leftL disjoint_add_leftR)

lemma disjointness_right_plus_eq[simp]:
  \<open>b ## c \<Longrightarrow> a ## b + c \<longleftrightarrow> a ## b \<and> a ## c\<close>
  by (metis disjointness_right_plusI disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_double_assoc2:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> a ## d \<Longrightarrow> b ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (meson disjointness_right_plusI partial_add_double_assoc)

end

class disjoint_parts_multiunit_sep_alg = multiunit_sep_alg + disjoint_parts_perm_alg

class disjoint_parts_sep_alg = sep_alg + disjoint_parts_multiunit_sep_alg


section \<open> Trivial Self-disjointness Separation Algebra \<close>

class trivial_selfdisjoint_perm_alg = perm_alg +
  assumes selfdisjoint_same: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>
begin

text \<open> All selfdisjoint elements are duplicable \<close>

lemma all_selfdisjoint_dup:
  \<open>a ## a \<Longrightarrow> sepadd_dup a\<close>
  using selfdisjoint_same sepadd_dup_def by presburger

end

context strong_sep_perm_alg
begin
(* trivial selfdisjointness is a subclass of strong separation *)
subclass trivial_selfdisjoint_perm_alg
  by standard (simp add: selfsep_iff)

end

class trivial_selfdisjoint_multiunit_sep_alg = multiunit_sep_alg + trivial_selfdisjoint_perm_alg

class trivial_selfdisjoint_sep_alg = sep_alg + trivial_selfdisjoint_multiunit_sep_alg


section \<open> Cross-Split Separation Algebra \<close>

class crosssplit_perm_alg = perm_alg +
  assumes cross_split:
  \<open>a ## b \<Longrightarrow> c ## d \<Longrightarrow> a + b = c + d \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
      ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>

class crosssplit_multiunit_sep_alg = multiunit_sep_alg + crosssplit_perm_alg

class crosssplit_sep_alg = sep_alg + crosssplit_multiunit_sep_alg


section \<open> Cancellative Separation Algebras\<close>

class cancel_perm_alg = perm_alg +
  assumes partial_right_cancel[simp]: \<open>\<And>a b c. a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
begin

lemma partial_right_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
  using partial_right_cancel disjoint_sym
  by force

lemma partial_left_cancel[simp]:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  by (metis partial_add_commute partial_right_cancel)

lemma partial_left_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  using partial_left_cancel disjoint_sym
  by force

lemmas partial_right_cancelD = iffD1[OF partial_right_cancel, rotated 2]
lemmas partial_right_cancel2D = iffD1[OF partial_right_cancel2, rotated 2]
lemmas partial_left_cancelD = iffD1[OF partial_left_cancel, rotated 2]
lemmas partial_left_cancel2D = iffD1[OF partial_left_cancel2, rotated 2]

lemma cancel_right_to_unit:
  assumes
    \<open>a ## b\<close>
    \<open>a + b = b\<close>
  shows \<open>sepadd_unit a\<close>
  unfolding sepadd_unit_def_strong
proof (intro conjI allI impI)
  show Daa: \<open>a ## a\<close>
    using assms
    by (metis disjoint_add_rightL)

  fix c
  assume D0:
    \<open>a ## c\<close>

  have E1: \<open>a = a + a\<close>
  proof -
    have \<open>b ## a + a\<close>
      using assms
      by (simp add: disjoint_add_swap_rl disjoint_sym)
    moreover have \<open>b + a = b + (a + a)\<close>
      using assms
      by (metis partial_add_assoc3 partial_add_commute disjoint_add_swap_rl disjoint_sym)
    ultimately show ?thesis
      using assms
      by (simp add: disjoint_sym_iff)
  qed

  have D1: \<open>c + a ## a\<close>
    using assms D0 E1 Daa
    by (metis disjoint_add_left_commute)

  have \<open>a + c = a + (c + a)\<close>
    using assms D0 E1 Daa
    by (metis partial_add_assoc partial_add_commute)
  then show \<open>a + c = c\<close>
    using D0 D1
    by (metis partial_left_cancelD disjoint_sym partial_add_commute)
qed

lemma cancel_left_to_unit:
  \<open>a ## b \<Longrightarrow> a + b = a \<Longrightarrow> sepadd_unit b\<close>
  by (metis cancel_right_to_unit disjoint_sym partial_add_commute)


subsection \<open> Separation Logic \<close>

text \<open> cancellability is a weak form of sepconj-conj distributivity \<close>
lemma sepconj_conj_distrib_eqpred:
  \<open>sepconj_conj_distrib ((=) x)\<close>
  by (force simp add: sepconj_conj_distrib_def fun_eq_iff sepconj_iff)

lemma precise_then_sepconj_conj_distrib:
  \<open>precise P \<Longrightarrow> sepconj_conj_distrib P\<close>
  apply (clarsimp simp add: precise_def sepconj_conj_distrib_def sepconj_def fun_eq_iff)
  apply (metis partial_le_plus partial_left_cancel2D)
  done

lemma sepconj_conj_distrib_then_precise:
  assumes P_has_units: \<open>\<And>x. P x \<Longrightarrow> \<exists>u. x ## u \<and> sepadd_unit u\<close>
  shows \<open>sepconj_conj_distrib P \<Longrightarrow> precise P\<close>
  apply (clarsimp simp add: precise_def sepconj_conj_distrib_def sepconj_def le_fun_def
      imp_ex_conjL imp_conjL less_eq_sepadd_def')
  apply (intro conjI impI allI)
    apply clarsimp
    apply (frule_tac ?x1=\<open>h2 + _\<close> in P_has_units)
    apply clarsimp
    apply (rename_tac h2 w u)
    apply (drule_tac x=\<open>(=) (w + u)\<close> and y=\<open>(=) u\<close> in spec2)
    apply (metis disjoint_add_leftR sepadd_unit_right)
   apply clarsimp
   apply (frule_tac ?x1=\<open>h1 + _\<close> in P_has_units)
   apply clarsimp
   apply (rename_tac h2 w u)
   apply (drule_tac x=\<open>(=) (w + u)\<close> and y=\<open>(=) u\<close> in spec2)
   apply (metis disjoint_add_leftR sepadd_unit_right)
  apply (rename_tac hp1 hp2 hq1 hq2)
  apply (drule_tac x=\<open>(=) hq1\<close> and y=\<open>(=) hq2\<close> in spec2)
  apply force
  done

lemma precise_iff_conj_distrib:
  assumes \<open>\<And>x. P x \<longrightarrow> (\<exists>u. u ## x \<and> sepadd_unit u)\<close>
  shows \<open>precise P \<longleftrightarrow> sepconj_conj_distrib P\<close>
  using assms
  by (meson disjoint_sym_iff precise_then_sepconj_conj_distrib sepconj_conj_distrib_then_precise)

end

class cancel_multiunit_sep_alg = cancel_perm_alg + multiunit_sep_alg
begin

lemma selfsep_selfadd_iff_unit:
  \<open>a ## a \<and> a + a = a \<longleftrightarrow> sepadd_unit a\<close>
  by (metis partial_right_cancelD unitof_disjoint2 unitof_inherits_disjointness unitof_is_unit2
      unitof_is_sepadd_unit unitof_sepadd_unit)

lemma strong_positivity:
  \<open>a ## b \<Longrightarrow> c ## c \<Longrightarrow> a + b = c \<Longrightarrow> c + c = c \<Longrightarrow> a = b \<and> b = c\<close>
  by (metis add_sepadd_unit_add_iff_parts_sepadd_unit cancel_right_to_unit disjoint_units_identical
      sepadd_unit_right)

lemma \<open>(a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>) \<le> ((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top>\<close>
  nitpick[card=4]
  oops

lemma \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
proof -
  have F1: \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> = (a \<^emph> b) \<^emph> \<top> \<squnion> (a \<sqinter> b) \<^emph> \<top>\<close>
    by (simp add: sepconj_comm sepconj_pdisj_distrib_left)
  moreover have \<open>a \<^emph> b \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (metis le_infI sepconj_comm sepconj_middle_monotone_lhsL2 top_greatest)
  moreover have \<open>(a \<sqinter> b) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (simp add: sepconj_monoL)
  ultimately show ?thesis
    by simp
qed

lemma precise_implies_unitlikes_are_units:
  \<open>precise P \<Longrightarrow> (\<forall>h u. P h \<longrightarrow> h ## u \<longrightarrow> P (h + u) \<longrightarrow> sepadd_unit u)\<close>
  by (meson cancel_left_to_unit less_eq_sepadd_def partial_le_plus precise_def)

end

class cancel_sep_alg = cancel_multiunit_sep_alg + sep_alg


section \<open> No-unit perm alg \<close>

text \<open>
  Here we create a perm_alg without any unit.
  Such an algebra is necessary to prove permission heaps are cancellative.
\<close>
class no_unit_perm_alg = perm_alg +
  assumes no_units: \<open>\<not> sepadd_unit a\<close>

class cancel_no_unit_perm_alg = no_unit_perm_alg + cancel_perm_alg
begin

lemma no_unit_cancel_rightD[dest]:
  \<open>a ## b \<Longrightarrow> a + b = b \<Longrightarrow> False\<close>
  using cancel_right_to_unit no_units by blast

lemma no_unit_cancel_leftD[dest]:
  \<open>a ## b \<Longrightarrow> a + b = a \<Longrightarrow> False\<close>
  using cancel_left_to_unit no_units by blast

end


section \<open> Halving separation algebra \<close>

class halving_perm_alg = perm_alg +
  fixes half :: \<open>'a \<Rightarrow> 'a\<close>
  assumes half_additive_split: \<open>\<And>a. half a + half a = a\<close>
  assumes half_self_disjoint: \<open>\<And>a. half a ## half a\<close>
  assumes half_sepadd_distrib: \<open>\<And>a b. a ## b \<Longrightarrow> half (a + b) = half a + half b\<close>
begin

lemma half_disjoint_preservation_left: \<open>a ## b \<Longrightarrow> half a ## b\<close>
  by (metis disjoint_add_leftR half_additive_split half_self_disjoint)

lemma half_disjoint_preservation_right: \<open>a ## b \<Longrightarrow> a ## half b\<close>
  using half_disjoint_preservation_left disjoint_sym by blast

lemma half_disjoint_preservation: \<open>a ## b \<Longrightarrow> half a ## half b\<close>
  by (simp add: half_disjoint_preservation_left half_disjoint_preservation_right)


lemma half_disjoint_distribL:
  \<open>a ## c \<Longrightarrow> a + c ## b \<Longrightarrow> a + half c ## b + half c\<close>
  by (metis disjoint_add_leftL disjoint_add_right_commute disjoint_sym half_additive_split
      half_self_disjoint partial_add_assoc)

lemma half_disjoint_distribR:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + half c ## b + half c\<close>
  using half_disjoint_distribL disjoint_sym by blast

lemma half_eq_full_imp_self_additive:
  \<open>half a = a \<Longrightarrow> a + a = a\<close>
  by (metis half_additive_split)

end

class halving_multiunit_sep_alg = multiunit_sep_alg + halving_perm_alg

class halving_sep_alg = sep_alg + halving_multiunit_sep_alg


subsection \<open> Trivial self-disjoint + halving (very boring) \<close>

class trivial_halving_perm_alg = trivial_selfdisjoint_perm_alg + halving_perm_alg
begin

lemma trivial_half[simp]: \<open>half a = a\<close>
  by (simp add: selfdisjoint_same half_additive_split half_self_disjoint)

lemma all_duplicable:
  \<open>sepadd_dup x\<close>
  using all_selfdisjoint_dup half_self_disjoint
  by auto

end


section \<open> All-disjoint algebra \<close>

text \<open>
  This seems very strong, but the discrete algebra is this sort
  of algebra, and it's the necessary precondition to build up Error.
\<close>

class all_disjoint_perm_alg = perm_alg +
  assumes all_disjoint[simp]: \<open>a ## b\<close>

class all_disjoint_multiunit_sep_alg =
  multiunit_sep_alg + all_disjoint_perm_alg

class all_disjoint_sep_alg =
  sep_alg + all_disjoint_perm_alg


section \<open> Bibliography \<close>

text \<open>
  [KKB2012] Klein, Gerwin, Rafal Kolanski, and Andrew Boyton. 2012.
      "Mechanised Separation Algebra." ITP 2012.
      \<^url>\<open>https://doi.org/10.1007/978-3-642-32347-8_22\<close>.

  [VSTBook2014] Appel, Andrew W., Robert Dockins, Aquinas Hobor, Lennart Beringer, Josiah Dodds,
      Gordon Stewart, Sandrine Blazy, and Xavier Leroy.
      2014. "Chapter 6 - Separation Algebras."
      In Program Logics for Certified Compilers, 1st ed. Cambridge University Press.
      \<^url>\<open>https://doi.org/10.1017/CBO9781107256552\<close>.

  [BHK2018] Bannister, Callum, Peter Höfner, and Gerwin Klein.
      2018. "Backwards and Forwards with Separation Logic." ITP 2018.
      \<^url>\<open>https://doi.org/10.1007/978-3-319-94821-8_5\<close>.
\<close>

end