theory Destab
  imports "../SepAlgInstances"
begin


section \<open> Authoratative Algebra \<close>

(* see excl *)
typedef(overloaded) ('a::pre_perm_alg) auth =
  \<open>{(ma::'a excl, a'::'a). ma \<noteq> None \<longrightarrow> a' \<preceq> the_excl ma}\<close>
  by blast
setup_lifting type_definition_auth

instantiation auth :: (pre_perm_alg) disjoint
begin
lift_definition disjoint_auth :: \<open>'a auth \<Rightarrow> 'a auth \<Rightarrow> bool\<close> is
  \<open>\<lambda>(ma,a') (mb,b').
    ma ## mb \<and> a' ## b' \<and>
    (ma \<noteq> None \<longrightarrow> a' + b' \<preceq> the_excl ma) \<and>
    (mb \<noteq> None \<longrightarrow> a' + b' \<preceq> the_excl mb)\<close> .
instance by standard
end

instantiation auth :: (pre_perm_alg) plus
begin
lift_definition plus_auth :: \<open>'a auth \<Rightarrow> 'a auth \<Rightarrow> 'a auth\<close> is
  \<open>\<lambda>(ma,a') (mb,b').
    if ma \<noteq> None \<and> mb \<noteq> None then (ma,a')
    else if ma \<noteq> None \<and> mb = None then
      (if a' + b' \<preceq> the_excl ma then (ma, a'+b') else (ma,a'))
    else if ma = None \<and> mb \<noteq> None then
      (if a' + b' \<preceq> the_excl mb then (mb, a'+b') else (mb,b'))
    else (ma + mb, a' + b')\<close>
  by (force simp add: plus_option_iff split: if_splits)
instance by standard
end

instance auth :: (pre_perm_alg) pre_perm_alg
  apply standard
      apply transfer
      apply clarsimp
      apply (elim disjE; simp?)
         apply (metis partial_add_assoc)
        apply (simp add: partial_add_assoc)  
  sorry

instance auth :: (\<open>{pre_perm_alg, positivity_law}\<close>) positivity_law
  apply standard
  apply transfer
  apply (clarsimp split: if_splits)
   apply (metis positivity)
  apply (metis positivity)
  done

instance "fun" :: (type, perm_alg) perm_alg
  by standard

lemma fun_positivity_alt:
  fixes a c1 c2 :: \<open>'a \<Rightarrow> 'b::positivity_law\<close>
  shows \<open>a ## c1 \<Longrightarrow> a + c1 ## c2 \<Longrightarrow> a + c1 + c2 = a \<Longrightarrow> a + c1 = a\<close>
  by (simp add: plus_fun_def disjoint_fun_def fun_eq_iff, metis positivity)

lemma less_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<noteq> g x) \<and> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_sepadd_def' fun_eq_iff disjoint_fun_def, metis)

lemma less_eq_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x = g x) \<or> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_eq_sepadd_def disjoint_fun_def fun_eq_iff, metis)

lemma fun_all_unit_elems_then_unit:
  \<open>\<forall>x. sepadd_unit (f x) \<Longrightarrow> sepadd_unit f\<close>
  by (simp add: disjoint_fun_def plus_fun_def sepadd_unit_def_strong)

instantiation "fun" :: (type, pre_multiunit_sep_alg) pre_multiunit_sep_alg
begin
definition unitof_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>unitof_fun f \<equiv> \<lambda>x. unitof (f x)\<close>
declare unitof_fun_def[simp]

instance
  by standard
    (simp add: disjoint_fun_def plus_fun_def le_fun_def fun_eq_iff le_iff_sepadd; metis)+
end

instantiation "fun" :: (type, multiunit_sep_alg) multiunit_sep_alg
begin

instance by standard

lemma less_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<prec> g x) \<and> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis le_iff_part_of less_sepadd_fun_eq resource_order.less_le)

lemma less_eq_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis less_sepadd_fun_eq2 less_eq_sepadd_fun_eq resource_order.le_less)

end

instantiation "fun" :: (type, pre_sep_alg) pre_sep_alg
begin

definition zero_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>zero_fun \<equiv> \<lambda>x. 0\<close>
declare zero_fun_def[simp]

instance
  by standard
    (fastforce simp add: fun_eq_iff less_eq_sepadd_fun_eq2)+

end

instance "fun" :: (type, sep_alg) sep_alg
  by standard


subsection \<open> Extended instances \<close>

instance "fun" :: (type, dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff,
      metis dup_sub_closure)

(* not allcompatible_perm_alg *)

instance "fun" :: (type, strong_sep_pre_perm_alg) strong_sep_pre_perm_alg
  by standard
    (clarsimp simp add: disjoint_fun_def plus_fun_def fun_eq_iff selfsep_iff
      fun_all_unit_elems_then_unit)

instance "fun" :: (type, disjoint_parts_pre_perm_alg) disjoint_parts_pre_perm_alg
  by standard (simp add: disjoint_fun_def)

instance "fun" :: (type, trivial_selfdisjoint_pre_perm_alg) trivial_selfdisjoint_pre_perm_alg
  by standard
    (force dest: selfdisjoint_same simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

instance "fun" :: (type, crosssplit_pre_perm_alg) crosssplit_pre_perm_alg
proof standard
  fix a b c d :: \<open>'a \<Rightarrow> 'b\<close>
  assume
    \<open>a ## b\<close>
    \<open>c ## d\<close>
    \<open>a + b = c + d\<close>
  then have assms2:
    \<open>\<forall>x. a x ## b x\<close>
    \<open>\<forall>x. c x ## d x\<close>
    \<open>\<forall>x. a x + b x = c x + d x\<close>
    by (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)+
  then have \<open>\<forall>x. \<exists>acx adx bcx bdx.
      acx ## adx \<and> bcx ## bdx \<and> acx ## bcx \<and> adx ## bdx \<and>
      a x = acx + adx \<and> b x = bcx + bdx \<and>
      c x = acx + bcx \<and> d x = adx + bdx\<close>
    using cross_split[of \<open>a x\<close> \<open>b x\<close> \<open>c x\<close> \<open>d x\<close> for x]
    by metis
  then show
    \<open>\<exists>ac ad bc bd.
        ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
        ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>
    by (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis)
qed

instance "fun" :: (type, cancel_pre_perm_alg) cancel_pre_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

(* not no_unit_pre_perm_alg *)

instantiation "fun" :: (type, halfof) halfof
begin
definition \<open>halfof_fun (f :: 'a \<Rightarrow> 'b) \<equiv> \<lambda>x. halfof (f x)\<close>
instance ..
end

instance "fun" :: (type, halving_pre_perm_alg) halving_pre_perm_alg
  by standard
    (simp add: halfof_fun_def disjoint_fun_def plus_fun_def fun_eq_iff
      halfof_additive_split halfof_self_disjoint halfof_sepadd_distrib)+

instance "fun" :: (type, all_disjoint_pre_perm_alg) all_disjoint_pre_perm_alg
  by standard (simp add: disjoint_fun_def)+


end