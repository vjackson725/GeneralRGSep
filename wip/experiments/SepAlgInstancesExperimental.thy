theory SepAlgInstancesExperimental
  imports "../../SepAlgInstances" "HOL-Library.Type_Length"
begin


section \<open> Error Resources #2 \<close>

text \<open>
  An error state for every maximal resource.
\<close>
typedef(overloaded) ('a::pre_perm_alg) error_res =
  \<open>Inl ` (UNIV :: 'a set) \<union> Inr ` {a::'a. \<nexists>b. (b \<succ> a)}\<close>
  by blast

setup_lifting type_definition_error_res


instantiation error_res :: (pre_perm_alg) disjoint
begin
lift_definition disjoint_error_res :: \<open>'a error_res \<Rightarrow> 'a error_res \<Rightarrow> bool\<close> is
  \<open>\<lambda>(a::'a + 'a) (b::'a + 'a).
    (\<exists>xa xb. a = Inr xa \<and> b = Inr xb \<and> xa ## xb) \<or>
    (\<exists>ea xb. a = Inr ea \<and> b = Inl xb \<and> xb \<preceq> ea) \<or>
    (\<exists>xa eb. a = Inl xa \<and> b = Inr eb \<and> xa \<preceq> eb) \<or>
    (\<exists>e. a = Inr e \<and> b = Inr e)\<close> .
instance ..
end

instantiation error_res :: (pre_perm_alg) plus
begin
lift_definition plus_error_res :: \<open>'a error_res \<Rightarrow> 'a error_res \<Rightarrow> 'a error_res\<close> is
  \<open>\<lambda>(a::'a + 'a) (b::'a + 'a).
    case a of
      Inl x \<Rightarrow>
        (case b of
          Inl y \<Rightarrow> Inl (x + y)
        | Inr e \<Rightarrow> Inr e)
    | Inr e \<Rightarrow> Inr e\<close>
  by (force split: sum.splits)
instance ..
end


lemma
  fixes a b c :: \<open>('a::{perm_alg}) error_res\<close>
  shows \<open>
    R = {(a,b,a+b)|a b::'a. a ## b} \<Longrightarrow>
    Re = {(a,b,a+b)|a b::'a error_res. a ## b} \<Longrightarrow>
    BC = {(b,c)|b c::'a error_res. b ## c} \<Longrightarrow>
    ApBC = {(a,b+c)|a b c::'a error_res. b ## c \<and> a ## b + c} \<Longrightarrow>
    AB = {(a,b)|a b::'a error_res. a ## b} \<Longrightarrow>
    b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  nitpick[card 'a=1]
  sorry

\<comment> \<open> requires positivity_law \<close>
instance error_res :: (\<open>{pre_perm_alg, positivity_law}\<close>) pre_perm_alg
  apply standard
      apply (transfer, clarsimp split: sum.splits; fail)
     apply (transfer, clarsimp split: sum.splits)
     apply (elim disjE; blast?)
     apply (clarsimp simp add: less_sepadd_def)
     apply (metis disjoint_sym partial_add_commute positivity)
    apply (transfer, force dest: disjoint_sym)
  subgoal sorry
  apply (transfer, clarsimp split: sum.splits)
   apply (elim disjE; blast?)
   apply clarsimp
   apply (meson partial_le_part_left partial_le_plus2
      resource_preordering.strict_iff_not resource_preordering.trans)
  oops


instance error_res :: (\<open>{pre_perm_alg, positivity_law}\<close>) positivity_law
  apply standard
      apply (transfer, clarsimp split: sum.splits; fail)
     apply (transfer, clarsimp split: sum.splits)
  sledgehammer
  done

end


section \<open> Locked resources \<close>

(* This doesn't work. *)

(* TODO: this might be better as a datatype. *)
type_synonym 'a locked = \<open>munit + 'a\<close>

abbreviation(input) \<open>Locked \<equiv> Inl \<one> :: 'a locked\<close>
abbreviation(input) \<open>Unlocked x \<equiv> Inr x :: 'a locked\<close>

lemma disjoint_locked_simps[simp]:
  \<open>\<And>b. Locked ## b \<longleftrightarrow> False\<close>
  \<open>\<And>a. a ## Locked \<longleftrightarrow> False\<close>
  \<open>\<And>a b. Unlocked a ## Unlocked b \<longleftrightarrow> a ## b\<close>
    apply (case_tac b; simp)
   apply (case_tac a; simp)
  apply simp
  done

type_synonym 'a resources = \<open>nat \<rightharpoonup> 'a locked\<close>


section \<open> Max algebra \<close>

typedef(overloaded) ('a::order) max_res =
  \<open>{x::'a\<times>'a. fst x \<le> snd x}\<close>
  by auto

setup_lifting type_definition_max_res

instantiation max_res :: (canonically_ordered_monoid_add) perm_alg
begin

lift_definition disjoint_max_res :: \<open>'a max_res \<Rightarrow> 'a max_res \<Rightarrow> bool\<close> is
  \<open>\<lambda>x y. snd x = snd y\<close> .

lift_definition plus_max_res :: \<open>'a max_res \<Rightarrow> 'a max_res \<Rightarrow> 'a max_res\<close> is
  \<open>\<lambda>(x,m) (y,_). (min (x + y) m, m)\<close>
  by (clarsimp simp add: min_def split: prod.splits)

instance
  apply standard
  subgoal
    apply transfer
    apply (clarsimp simp add: min_def split: prod.splits)
    apply (intro conjI impI allI)
                        apply (metis add.commute add.left_commute)
                        apply (metis add.commute add.left_commute le_iff_add)
                       apply (metis add.commute add.left_commute)
                      apply (metis add.commute add.left_commute)
                     apply (metis add.commute add.left_commute)
                    apply (metis add.commute add.left_commute le_iff_add)
                   apply (metis add.commute add.left_commute)
                  apply (metis add.commute add.left_commute)
                 apply (metis add.commute add.left_commute)
                apply (metis order_eq_iff le_iff_add)
               apply (metis add.commute add.left_commute)
              apply (metis add.commute add.left_commute le_iff_add)
             apply (metis add.commute add.left_commute le_iff_add)
            apply (metis add.commute add.left_commute le_iff_add)
           apply (metis add.commute add.left_commute le_iff_add)
          apply (metis add.commute add.left_commute le_iff_add)
         apply (metis add.commute add.left_commute le_iff_add)
        apply (metis add.commute add.left_commute le_iff_add)
       apply (metis add.commute add.left_commute le_iff_add)
      apply (metis add.commute add.left_commute le_iff_add)
     apply (metis add.commute add.left_commute le_iff_add)
    apply (metis add.commute le_iff_add order_eq_iff)
    done
      apply (transfer, clarsimp simp add: add.commute split: prod.splits; fail)
     apply (transfer, simp; fail)
    apply (transfer, simp split: prod.splits; fail)
   apply (transfer, clarsimp split: prod.splits; fail)
  apply (transfer, clarsimp split: prod.splits, metis le_iff_add min_absorb2 min_def)
  done

end


lemma nat_ratio_leq_trans:
  fixes n1 :: nat
  assumes
    \<open>0 < n2\<close>
    \<open>n1 * d2 \<le> n2 * d1\<close>
    \<open>n2 * d3 \<le> n3 * d2\<close>
  shows
    \<open>n1 * d3 \<le> n3 * d1\<close>
proof -
  have \<open>n1 * n3 * d2 \<le> n2 * n3 * d1\<close>
    using assms(2) by simp
  moreover have \<open>n1 * n2 * d3 \<le> n1 * n3 * d2\<close>
    using assms(3) by simp
  ultimately have \<open>n1 * n2 * d3 \<le> n2 * n3 * d1\<close>
    using le_trans by blast
  then show ?thesis
    using assms(1) by simp
qed


section \<open> Lists (component-wise) \<close>

instantiation list :: (pre_perm_alg) pre_perm_alg
begin

definition disjoint_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>disjoint_list a b \<equiv> list_all2 (##) a b\<close>

definition plus_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>plus_list a b \<equiv> map2 (+) a b\<close>

instance
  apply standard
      apply (clarsimp simp add: disjoint_list_def plus_list_def list_all2_conv_all_nth
      list_eq_iff_nth_eq, metis partial_add_assoc)
     apply (clarsimp simp add: disjoint_list_def plus_list_def list_all2_conv_all_nth
      list_eq_iff_nth_eq, metis partial_add_commute)
    apply (clarsimp simp add: disjoint_list_def list_all2_conv_all_nth, metis disjoint_sym)
   apply (clarsimp simp add: disjoint_list_def plus_list_def list_all2_conv_all_nth
      list_eq_iff_nth_eq, metis disjoint_add_rightL)
   apply (clarsimp simp add: disjoint_list_def plus_list_def list_all2_conv_all_nth
      list_eq_iff_nth_eq, metis disjoint_add_right_commute)
  done

end

instance list :: (perm_alg) perm_alg
  by standard
    (clarsimp simp add: disjoint_list_def plus_list_def list_all2_conv_all_nth list_eq_iff_nth_eq,
      metis positivity)


section \<open> Limited Fraction permission algebra \<close>

(* fractions with a bounded denominator *)
typedef(overloaded) ('a::len) lfrac =
  \<open>{(n::nat,d::nat). gcd n d = 1 \<and> 0 < n \<and> n \<le> d \<and> d \<le> LENGTH('a)}\<close>
  morphisms Rep_lfrac LFrac
  by (rule exI[of _ \<open>(1,1)\<close>], simp add: Suc_leI)

setup_lifting type_definition_lfrac

lift_definition lfrac_divsr :: \<open>('a::len) lfrac \<Rightarrow> nat\<close> is \<open>snd\<close> .
lift_definition lfrac_numer :: \<open>('a::len) lfrac \<Rightarrow> nat\<close> is \<open>fst\<close> .

subsection \<open> helper lemmas \<close>

subsection \<open> instances\<close>

instantiation lfrac :: (len) order
begin

lift_definition less_eq_lfrac :: \<open>('a::len) lfrac \<Rightarrow> 'a lfrac \<Rightarrow> bool\<close> is
  \<open>\<lambda>(n1,d1) (n2,d2). n1 * d2 \<le> n2 * d1\<close> .

lift_definition less_lfrac :: \<open>('a::len) lfrac \<Rightarrow> 'a lfrac \<Rightarrow> bool\<close> is
  \<open>\<lambda>(n1,d1) (n2,d2). n1 * d2 < n2 * d1\<close> .

instance
  apply standard
     apply (transfer, clarsimp split: prod.splits, linarith)
    apply (transfer, clarsimp split: prod.splits)
   apply (transfer, clarsimp split: prod.splits, metis nat_ratio_leq_trans)
  apply (transfer, clarsimp split: prod.splits,
      drule coprime_crossproduct_nat[simplified coprime_iff_gcd_eq_1, THEN iffD1, rotated 2]; presburger)
  done

end


subsection \<open> Strip Units \<close>

text \<open> Resource algebra transformer that strips the units from the given algebra. \<close>

(* TODO: This doesn't really work due to needing \<open>(+)\<close> to be total. *)

typedef(overloaded) ('a::pre_perm_alg) strip_units =
  \<open>if \<exists>a::'a. \<not> sepadd_unit a then {a::'a. \<not> sepadd_unit a} else UNIV\<close>
  by force

setup_lifting type_definition_strip_units

subsection \<open> perm_alg \<close>

instantiation strip_units :: (\<open>perm_alg\<close>) perm_alg
begin

lift_definition disjoint_strip_units :: \<open>'a strip_units \<Rightarrow> 'a strip_units \<Rightarrow> bool\<close>
  is \<open>(##)\<close> .

lift_definition plus_strip_units :: \<open>'a strip_units \<Rightarrow> 'a strip_units \<Rightarrow> 'a strip_units\<close>
  is \<open>\<lambda>a b. if a ## b then a + b else undefined\<close>
  apply (clarsimp simp add: split: if_splits)
  sorry

instance
  apply standard
(*
       apply (transfer, metis partial_add_assoc)
      apply (transfer, metis partial_add_commute)
     apply (transfer, metis disjoint_sym_iff)
    apply (transfer, metis disjoint_add_rightL)
   apply (transfer, metis disjoint_add_right_commute)
  apply (transfer, metis positivity)
  done
*)
  sorry

end


lemma strip_units_one_greatest:
  fixes a :: \<open>'a::linordered_semidom strip_units\<close>
  shows \<open>a \<preceq> 1\<close>
  unfolding less_eq_sepadd_def
  apply (transfer, clarsimp)
  apply (metis add_diff_cancel_left' le_add_diff_inverse2 le_numeral_extra(4)
      linordered_semidom_ge0_le_iff_add)
  done

subsection \<open> Extended instances \<close>

instance strip_units :: (\<open>{linordered_semiring,zero_less_one}\<close>) dupcl_perm_alg
  by standard
    (transfer, simp add: add_nonneg_eq_0_iff)

instance strip_units :: (linordered_semidom) allcompatible_perm_alg
  by standard 
    (simp add: compatible_def,
      metis compatible_def strip_units_one_greatest trans_le_ge_is_compatible)

(* not a strong_sep_perm_alg *)

(* not a disjoint_parts_perm_alg *)

(* not a trivial_selfdisjoint_perm_alg *)

(* not a crosssplit_perm_alg *)

instance strip_units :: (\<open>{linordered_semiring,zero_less_one}\<close>) cancel_perm_alg
  by standard (transfer, force)

(* not a no_unit_perm_alg *)

instantiation strip_units :: (linordered_field) halving_perm_alg
begin
lift_definition half_strip_units :: \<open>'a strip_units \<Rightarrow> 'a strip_units\<close> is \<open>\<lambda>x. x / 2\<close> by simp
instance  by standard (transfer, simp)+
end

(* not an all_disjoint_perm_alg *)


subsection \<open> perm_alg \<close>

lemma nat_gcd_div_distrib:
  fixes a b x :: nat
  shows \<open>x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> gcd a b div x = gcd (a div x) (b div x)\<close>
  by (smt (verit, best) Euclidean_Rings.div_eq_0_iff dvd_mult_div_cancel gcd_mult_distrib_nat
      gcd_nat.eq_neutr_iff nonzero_mult_div_cancel_left)

lemma nat_gcd_div_left_eq:
  fixes a b x :: nat
  shows \<open>c dvd a \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b \<Longrightarrow> gcd (a div c) b = gcd a (b * c) div c\<close>
  by (force simp add: nat_gcd_div_distrib)

lemma nat_gcd_div_right_eq:
  fixes a b x :: nat
  shows \<open>c dvd b \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b \<Longrightarrow> gcd a (b div c) = gcd (a * c) b div c\<close>
  by (force simp add: nat_gcd_div_distrib)

lemma gcd_add_multL2:
  fixes a n k :: \<open>'a :: semiring_gcd\<close>
  shows \<open>gcd (a + n * m) m = gcd a m\<close>
  by (metis add.commute gcd.commute gcd_add_mult)

lemma gcd_nat_gt0_iff:
  fixes a b :: nat
  shows \<open>(0 < gcd a b) = (0 < a \<or> 0 < b)\<close>
  by simp

lemma gcd_crossmult_coprime_divisors_eq:
  fixes a b :: nat
  assumes
    \<open>gcd a b = 1\<close>
    \<open>gcd m a = 1\<close>
    \<open>gcd n b = 1\<close>
  shows \<open>gcd (m * b + n * a) (a * b) = 1\<close>
  using assms
  by (metis coprime_commute coprime_iff_gcd_eq_1 gcd_add_mult gcd_add_multL2
      gcd_mult_right_right_cancel)

(*
instantiation lfrac :: (len) perm_alg
begin

definition disjoint_lfrac_raw :: \<open>('a::len) itself \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>disjoint_lfrac_raw tt x y \<equiv>
    fst x * snd y + fst y * snd x \<le> snd x * snd y \<and>
    snd x * snd y div gcd (fst x * snd y + fst y * snd x) (snd x * snd y) \<le> LENGTH('a)\<close>

definition norm_lfrac_raw :: \<open>nat \<times> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>norm_lfrac_raw x \<equiv>
    ( fst x div gcd (fst x) (snd x)
    , snd x div gcd (fst x) (snd x))\<close>

lemma norm_lfrac_raw_idem[simp]:
  \<open>norm_lfrac_raw (norm_lfrac_raw x) = norm_lfrac_raw x\<close>
  unfolding norm_lfrac_raw_def
  by (simp, metis (no_types, lifting) div_mult2_eq dvd_mult_div_cancel gcd_dvd1 gcd_dvd2
      gcd_mult_distrib_nat)

lemma norm_crossmult_eq[simp]:
  \<open>norm_lfrac_raw (fst (norm_lfrac_raw x) * b + a * snd (norm_lfrac_raw x), snd (norm_lfrac_raw x) * b) =
    norm_lfrac_raw (fst x * b + a * snd x, snd x * b)\<close>
proof -
  { fix c d
    have
      \<open>((c div gcd c d) * b + a * (d div gcd c d)) div
          gcd (c div gcd c d * b + a * (d div gcd c d)) (d div gcd c d * b) =
       (c * b + a * d) div gcd c d div gcd ((c * b + a * d) div gcd c d) (d * b div gcd c d)\<close>
      by (simp add: div_mult_swap dvd_div_mult)
    also have \<open>... = (c * b + a * d) div gcd c d div ((gcd (c * b + a * d) (d * b)) div gcd c d)\<close>
      by (force simp add: nat_gcd_div_distrib)
    also have \<open>... = (c * b + a * d) div (gcd (c * b + a * d) (d * b))\<close>
      by (metis div_div_div_same dvd_add dvd_mult gcd_dvd2 gcd_nat.boundedI gcd_nat.cobounded1
          mult.commute)
    finally have
      \<open>((c div gcd c d) * b + a * (d div gcd c d)) div
          gcd (c div gcd c d * b + a * (d div gcd c d)) (d div gcd c d * b) =
       (c * b + a * d) div gcd (c * b + a * d) (d * b)\<close> .
  } note H1 = this

  { fix c d
    have
      \<open>d div gcd c d * b div gcd (c div gcd c d * b + a * (d div gcd c d)) (d div gcd c d * b) =
          (d*b div gcd c d) div (gcd ((c*b + a*d) div gcd c d) (d*b div gcd c d))\<close>
      by (simp add: div_mult_swap dvd_div_mult)
    also have \<open>... = (d*b div gcd c d) div ((gcd (c*b + a*d) (d*b)) div gcd c d)\<close>
      by (force simp add: nat_gcd_div_distrib)
    also have \<open>... = (d*b) div (gcd (c*b + a*d) (d*b))\<close>
      by (metis div_div_div_same dvd_add dvd_mult gcd_dvd2 gcd_nat.boundedI gcd_nat.cobounded1
          mult.commute)
    finally have
      \<open>d div gcd c d * b div gcd (c div gcd c d * b + a * (d div gcd c d)) (d div gcd c d * b) =
          (d*b) div (gcd (c*b + a*d) (d*b))\<close> .
  } note H2 = this

  show ?thesis
    unfolding norm_lfrac_raw_def
    using H1 H2
    by (clarsimp simp only: fst_conv snd_conv)
qed


lemma norm_crossmult_eq2[simp]:
  \<open>norm_lfrac_raw (a * snd (norm_lfrac_raw x) + fst (norm_lfrac_raw x) * b, b * snd (norm_lfrac_raw x)) =
    norm_lfrac_raw (a * snd x + fst x * b, b * snd x)\<close>
  by (metis add.commute mult.commute norm_crossmult_eq) (* slow *)


lift_definition disjoint_lfrac :: \<open>('a::len) lfrac \<Rightarrow> 'a lfrac \<Rightarrow> bool\<close> is
  \<open>disjoint_lfrac_raw TYPE('a)\<close> .

lift_definition plus_lfrac :: \<open>('a::len) lfrac \<Rightarrow> 'a lfrac \<Rightarrow> 'a lfrac\<close> is
  \<open>\<lambda>(n1,d1) (n2,d2).
    if disjoint_lfrac_raw TYPE('a) (n1,d1) (n2,d2)
    then norm_lfrac_raw ((n1*d2 + n2*d1), d1 * d2)
    else (1,1)\<close>
  unfolding disjoint_lfrac_raw_def norm_lfrac_raw_def
  apply (clarsimp simp del: algebraic_semidom_class.div_add split: if_splits)
  apply (rename_tac n1 d1 n2 d2)
  apply (intro conjI)
    (* subgoal 1 *)
    apply (force simp add: nat_gcd_div_distrib[symmetric])
    (* subgoal 2 *)
   apply (simp add: div_greater_zero_iff gcd_nat_gt0_iff dvd_imp_le; fail)
    (* subgoal 3 *)
  apply (metis div_le_mono)
  done

instance
  apply standard
       apply (transfer, clarsimp simp add: if_distrib case_prod_beta)
       apply safe
         apply (rule arg_cong[of _ _ norm_lfrac_raw])
         apply (simp add: add_mult_distrib2 combine_common_factor mult.commute)
   

  find_theorems \<open>(\<lambda>(x,y). _)\<close> fst snd
  sorry

end


subsection \<open> Extended instances \<close>

instance lfrac :: dupcl_perm_alg
  sorry

instance lfrac :: allcompatible_perm_alg
  sorry

(* not a strong_sep_perm_alg *)

(* not a disjoint_parts_perm_alg *)

(* not a trivial_selfdisjoint_perm_alg *)

(* not a crosssplit_perm_alg *)

instance lfrac :: cancel_perm_alg
  sorry

instance lfrac :: no_unit_perm_alg
  sorry

instantiation lfrac :: halving_perm_alg
begin
lift_definition half_lfrac :: \<open>lfrac \<Rightarrow> 'a lfrac\<close> is \<open>\<lambda>(x,n). (x / 2, n)\<close>
  sorry
instance
  sorry
end

(* not an all_disjoint_perm_alg *)

*)

section \<open> Many-zero Alg \<close>

datatype 'a mzero = V 'a | Z nat

subsection \<open> instances \<close>

subsubsection \<open> perm_alg \<close>

instantiation mzero :: (pre_perm_alg) pre_perm_alg
begin

definition disjoint_mzero :: \<open>'a mzero \<Rightarrow> 'a mzero \<Rightarrow> bool\<close> where
  \<open>disjoint_mzero a b \<equiv> (\<exists>k. a = Z k) \<or> (\<exists>k. b = Z k) \<or> (\<exists>x y. a = V x \<and> b = V y \<and> x ## y)\<close>

definition plus_mzero :: \<open>'a mzero \<Rightarrow> 'a mzero \<Rightarrow> 'a mzero\<close> where
  \<open>plus_mzero a b \<equiv>
    case (a, b) of
      (V a, V b) \<Rightarrow> V (a + b)
    | (V a, Z k) \<Rightarrow> V a
    | (Z k, V b) \<Rightarrow> V b
    | (Z m, Z n) \<Rightarrow> Z (max m n)\<close>

instance
  apply standard
      apply (simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)
      apply (intro conjI allI impI)
       apply (simp, metis partial_add_assoc)
      apply (simp; fail)
     apply (simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)
     apply (intro conjI allI impI)
      apply (simp, metis partial_add_commute)
     apply (simp; fail)
    apply (simp add: disjoint_mzero_def, metis disjoint_sym)
   apply (simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)
   apply (case_tac a; simp)
   apply (metis disjoint_add_rightL)
  apply (simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)
   apply (case_tac a; simp)
   apply (metis disjoint_add_right_commute)
  apply (case_tac a; simp)
  apply (metis disjoint_sym)
  done

end

instantiation mzero :: (perm_alg) perm_alg
begin

instance
  apply standard
  apply (simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)
  apply (metis positivity)
  done

end


lemma disjoint_mzero_simps[simp]:
  \<open>V a ## V b = a ## b\<close>
  \<open>x ## Z k\<close>
  \<open>Z k ## y\<close>
  by (simp add: disjoint_mzero_def)+

lemma plus_mzero_simps[simp]:
  \<open>V a + V b = V (a + b)\<close>
  \<open>V a + Z k = V a\<close>
  \<open>Z k + V b = V b\<close>
  \<open>Z m + Z n = Z (max m n)\<close>
  by (simp add: plus_mzero_def)+

lemma plus_mzero_eq_rev[simp]:
  \<open>Z m + y = Z k \<longleftrightarrow> (\<exists>n. y = Z n \<and> k = max m n)\<close>
  \<open>x + Z n = Z k \<longleftrightarrow> (\<exists>m. x = Z m \<and> k = max m n)\<close>
  by (force simp add: plus_mzero_def split: mzero.splits)+

lemma mzero_zero_linearity:
  \<open>(Z m \<preceq> Z n) \<or> (Z n \<preceq> Z m)\<close>
  by (simp add: less_eq_sepadd_def, metis max.commute max_def)

lemma ex_mzero_iff:
  \<open>(\<exists>x::'a mzero. P x) \<longleftrightarrow> (\<exists>v. P (V v)) \<or> (\<exists>k. P (Z k))\<close>
  by (metis mzero.exhaust)

lemma less_eq_sepadd_mzero_eq:
  \<open>((x::('a::pre_perm_alg) mzero) \<preceq> y) =
    ((\<exists>a b. x = V a \<and> y = V b \<and> a \<preceq> b) \<or>
      (\<exists>m b. x = Z m \<and> y = V b) \<or>
      (\<exists>m n. x = Z m \<and> y = Z n \<and> m \<le> n))\<close>
  apply (cases x; cases y)
     apply (force simp add: less_eq_sepadd_def disjoint_mzero_def plus_mzero_def ex_mzero_iff)
    apply (force simp add: less_eq_sepadd_def disjoint_mzero_def plus_mzero_def ex_mzero_iff)
   apply (force simp add: less_eq_sepadd_def disjoint_mzero_def plus_mzero_def ex_mzero_iff)
  apply (simp add: less_eq_sepadd_def disjoint_mzero_def plus_mzero_def ex_mzero_iff,
      presburger)
  done

instantiation mzero :: (perm_alg) multiunit_sep_alg
begin

definition unitof_mzero :: \<open>'a mzero \<Rightarrow> 'a mzero\<close> where
  \<open>unitof_mzero \<equiv> \<lambda>_. Z 0\<close>

instance
  apply standard
   apply (simp add: unitof_mzero_def disjoint_mzero_def)
  apply (simp add: unitof_mzero_def plus_mzero_def split: mzero.splits)
  done

end


subsection \<open> Extended instances \<close>

instance mzero :: (dupcl_perm_alg) dupcl_perm_alg
  by (standard,
      simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits,
      meson dup_sub_closure)

instance mzero :: (allcompatible_perm_alg) allcompatible_perm_alg
proof standard
  fix a b :: \<open>'a mzero\<close>

  { fix x y :: \<open>'a mzero\<close>
    have
      \<open>(\<exists>a. x = V a \<and> (\<exists>b. y = V b \<and> a \<preceq> b)) \<or>
        (\<exists>m. x = Z m) \<and> (\<exists>b. y = V b) \<or>
        (\<exists>m. x = Z m \<and> (\<exists>n. y = Z n \<and> m \<le> n)) \<or>
        (\<exists>a. y = V a \<and> (\<exists>b. x = V b \<and> a \<preceq> b)) \<or>
        (\<exists>m. y = Z m) \<and> (\<exists>b. x = V b) \<or>
        (\<exists>m. y = Z m \<and> (\<exists>n. x = Z n \<and> m \<le> n)) \<longleftrightarrow>
          (\<forall>a b. x = V a  \<longrightarrow> y = V b \<longrightarrow> a \<preceq> b \<or> b \<preceq> a)\<close>
      by (cases x; cases y; force)
  }
  note H1 = this

  have \<open>(\<lambda>x y. \<forall>a. x = V a \<longrightarrow> (\<forall>b. y = V b \<longrightarrow> a \<preceq> b \<or> b \<preceq> a))\<^sup>*\<^sup>* a b\<close>
    by (rule rtranclp.rtrancl_into_rtrancl[of _ _ \<open>Z 0\<close>], blast, blast)
  then show \<open>compatible a b\<close>
    by (simp add: compatible_def less_eq_sepadd_mzero_eq sup_fun_def H1)
qed

(* not strong_sep_perm_alg *)

instance mzero :: (disjoint_parts_perm_alg) disjoint_parts_perm_alg
  by (standard, force simp add: disjoint_mzero_def plus_mzero_def split: mzero.splits)

instance mzero :: (trivial_selfdisjoint_perm_alg) trivial_selfdisjoint_perm_alg
  by (standard,
      force dest: selfdisjoint_same simp add: disjoint_mzero_def plus_mzero_def)

instance mzero :: (crosssplit_perm_alg) crosssplit_perm_alg
  oops

(* not a cancel_perm_alg *)
(* not a no_unit_perm_alg *)

instantiation mzero :: (halving_perm_alg) halving_perm_alg
begin
definition half_mzero :: \<open>'a mzero \<Rightarrow> 'a mzero\<close> where
  \<open>half_mzero x \<equiv> case x of V a \<Rightarrow> V (half a) | Z k \<Rightarrow> Z k\<close>

lemma half_mzero_simps[simp]:
  \<open>half (V a) = V (half a)\<close>
  \<open>half (Z k) = Z k\<close>
  by (simp add: half_mzero_def)+

instance
  apply standard
    apply (case_tac a; simp add: half_additive_split)
   apply (case_tac a; simp add: half_self_disjoint)
  apply (case_tac a; simp add: )
  sorry
end

(* not an all_disjoint_perm_alg *)


section \<open> Crash Algebra \<close>

lemma
  \<open>a ## b \<Longrightarrow> sepdomeq a a' \<Longrightarrow> sepdomeq (a + b) ab \<Longrightarrow> sepdomeq (a' + b) ab\<close>
  by (meson disjoint_add_leftR disjoint_add_swap_lr disjoint_add_swap_rl sepdomeq_def)

definition (in pre_perm_alg)
  \<open>sepdom_ec a \<equiv> Collect (sepdomeq a)\<close>

lemma (in pre_perm_alg) add_sepdom_ec_subseteq_sepdom_ec_add:
  \<open>a ## b \<Longrightarrow> {a' + b'|a' b'. a' \<in> sepdom_ec a \<and> b' \<in> sepdom_ec b} \<subseteq> sepdom_ec (a + b)\<close>
  apply (clarsimp simp add: sepdom_ec_def sepdomeq_def)
  apply (metis local.disjoint_add_leftR local.disjoint_add_swap_lr local.disjoint_sym_iff)
  done

lemma (in pre_perm_alg) add_sepdom_ec_subseteq_add_sepdom_ec_counterex:
  fixes a b :: 'a
  shows
    \<open>a ## b \<Longrightarrow>
    AB1 = {a' + b'|a' b'. a' \<in> sepdom_ec a \<and> b' \<in> sepdom_ec b} \<Longrightarrow>
    AB2 = sepdom_ec (a + b) \<Longrightarrow>
    AB2 \<subseteq> AB1\<close>
  apply (clarsimp simp add: sepdom_ec_def sepdomeq_def)
  nitpick[card 'a=2]
  oops

lemma (in pre_perm_alg)
  \<open>sepdomeq a b \<Longrightarrow> a ## c \<Longrightarrow> a + c ## d \<Longrightarrow> b + c ## d\<close>
  oops

typedef(overloaded) ('a::pre_perm_alg) wcrash =
  \<open>{(mh::'a option, K::'a set).
    \<comment> \<open> TODO: what's the closure condition here? \<close>
    \<comment> \<open> crashed resources are from a single sepdom \<close>
    (\<forall>a\<in>K. \<forall>b\<in>K. sepdomeq a b) \<and>
    \<comment> \<open> the non-crashed resource and the crashed resources are separate \<close>
    (\<forall>h. mh = Some h \<longrightarrow> (\<forall>a\<in>K. a ## h)) \<and>
    \<comment> \<open> the crash set never contains zero-like elements \<close>
    (\<forall>a\<in>K. \<forall>b. sepadd_zero b \<longrightarrow> \<not> sepdomeq a b) \<and>
    \<comment> \<open> something exists \<close>
    (mh = None \<longrightarrow> (\<exists>a. a \<in> K))
  }\<close>
  by blast

setup_lifting type_definition_wcrash

lift_definition mkres :: \<open>'a::pre_perm_alg \<Rightarrow> 'a wcrash\<close> is
  \<open>\<lambda>x. (Some x, {})\<close>
  by blast

lift_definition mkcrash :: \<open>'a::pre_perm_alg \<Rightarrow> 'a wcrash\<close> is
  \<open>\<lambda>x. if (\<exists>y. sepdomeq x y \<and> sepadd_zero y) then (Some x, {}) else (None, Collect (sepdomeq x))\<close>
  by (clarsimp, meson sepdomeq_reflI sepdomeq_sym sepdomeq_trans)

lift_definition getres :: \<open>('a::pre_perm_alg) wcrash \<Rightarrow> 'a option\<close> is
  \<open>fst\<close> .

lemma getres_mkres_eq[simp]: \<open>getres (mkres x) = Some x\<close>
  by (transfer, force)


subsection \<open> instances \<close>

subsubsection \<open> perm_alg \<close>

instantiation wcrash :: (multiunit_sep_alg) pre_perm_alg
begin

lift_definition disjoint_wcrash :: \<open>'a wcrash \<Rightarrow> 'a wcrash \<Rightarrow> bool\<close> is
  \<open>\<lambda>(ma, Ka) (mb, Kb).
    (\<forall>a. ma = Some a \<longrightarrow> (\<forall>b. mb = Some b \<longrightarrow> a ## b)) \<and>
    (\<forall>a. ma = Some a \<longrightarrow> (\<forall>b\<in>Kb. a ## b)) \<and>
    (\<forall>b. mb = Some b \<longrightarrow> (\<forall>a\<in>Ka. a ## b)) \<and>
    (\<forall>a\<in>Ka. \<forall>b\<in>Kb. a ## b)\<close> .

lemma sepdomeqL_subst_sepadd:
  \<open>x ## y \<Longrightarrow>
    sepdomeq x x' \<Longrightarrow>
    sepdomeq y y' \<Longrightarrow>
    sepdomeq (x + y) a \<Longrightarrow>
    sepdomeq (x' + y') a\<close>
  unfolding sepdomeq_def
  by (metis disjoint_add_leftL disjoint_add_swap_lr disjoint_sym_iff partial_add_commute)

lemma sepdomeqL_subst_sepaddL:
  \<open>x ## y \<Longrightarrow>
    sepdomeq x x' \<Longrightarrow>
    sepdomeq (x + y) a \<Longrightarrow>
    sepdomeq (x' + y) a\<close>
  using sepdomeqL_subst_sepadd by blast

lemma sepdomeqL_subst_sepaddR:
  \<open>x ## y \<Longrightarrow>
    sepdomeq y y' \<Longrightarrow>
    sepdomeq (x + y) a \<Longrightarrow>
    sepdomeq (x + y') a\<close>
  using sepdomeqL_subst_sepadd by blast


lift_definition plus_mzero :: \<open>'a wcrash \<Rightarrow> 'a wcrash \<Rightarrow> 'a wcrash\<close> is
  \<open>\<lambda>(ma, Ka) (mb, Kb).
    ((case (ma, mb) of
      (Some a, Some b) \<Rightarrow>
        (if
          a ## b \<and>
          (\<forall>a'\<in>Ka. \<forall>b'\<in>Kb. a' ## b' \<longrightarrow> a + b ## a' + b')
        then
          Some (a + b)
        else
          None)
    | (Some a, None) \<Rightarrow>
        (if (\<forall>a'\<in>Ka. \<forall>b'\<in>Kb. a' ## b' \<longrightarrow> a ## a' + b')
        then Some a
        else None)
    | (None, Some b) \<Rightarrow>
        (if (\<forall>a'\<in>Ka. \<forall>b'\<in>Kb. a' ## b' \<longrightarrow> b ## a' + b')
        then Some b
        else None)
    | (None, None) \<Rightarrow> None),
      {a + b|a b. a ## b \<and> a \<in> Ka \<and> b \<in> Kb \<and> (\<forall>z. sepadd_zero z \<longrightarrow> \<not> sepdomeq (a + b) z)})\<close>
  apply clarsimp
  apply (intro conjI impI allI)
     apply (metis sepdomeqL_subst_sepadd sepdomeq_reflI)
    apply (clarsimp split: option.splits if_splits; metis disjoint_sym)
   apply force
  oops


lemma plus_mkres_eq[simp]:
  \<open>a ## b \<Longrightarrow> mkres a + mkres b = mkres (a + b)\<close>
  oops


instance
  sorry

end
*)

end