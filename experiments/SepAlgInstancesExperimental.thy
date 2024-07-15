theory SepAlgInstancesExperimental
  imports "../SepAlgInstances" "HOL-Library.Type_Length"
begin


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


end