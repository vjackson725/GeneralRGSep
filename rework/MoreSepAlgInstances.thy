theory MoreSepAlgInstances
  imports SepAlgInstances
begin

class bounded_distrib_lattice = distrib_lattice + bounded_lattice

context boolean_algebra
begin
subclass bounded_distrib_lattice
  by standard
end

section \<open> lock permissions \<close>

text \<open>
  Krebber's (TODO cite) `lockable' permission structure.
\<close>

typedef ('a::bounded_distrib_lattice) lock_perm = \<open>UNIV :: 'a set\<close>
  by blast

definition \<open>Locked \<equiv> Abs_lock_perm \<bottom>\<close>
definition \<open>Unlocked \<equiv> Abs_lock_perm \<top>\<close>

declare Abs_lock_perm_inject[simplified, simp]
declare Abs_lock_perm_inverse[simplified, simp]
declare Rep_lock_perm_inverse[simplified, simp]

lemmas Rep_lock_perm_inject2 = Rep_lock_perm_inject[simplified]

lemma Abs_lock_perm_helpers:
  \<open>(a = Abs_lock_perm x) \<longleftrightarrow> x = Rep_lock_perm a\<close>
  \<open>(Abs_lock_perm x = a) \<longleftrightarrow> x = Rep_lock_perm a\<close>
  using Abs_lock_perm_inverse Rep_lock_perm_inject2
  by force+

setup_lifting type_definition_lock_perm

instantiation lock_perm :: (bounded_distrib_lattice) perm_alg
begin

lift_definition less_eq_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a = b \<or> (\<exists>c. a \<squnion> c = \<top> \<and> b = a \<sqinter> c)\<close> .

lift_definition less_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<noteq> b \<and> (\<exists>c. a \<squnion> c = \<top> \<and> b = a \<sqinter> c)\<close> .

lift_definition disjoint_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<squnion> b = \<top>\<close> .


lemma disjoint_lock_perm_simps[simp]:
  \<open>Locked ## b \<longleftrightarrow> b = Unlocked\<close>
  \<open>a ## Locked \<longleftrightarrow> a = Unlocked\<close>
  \<open>Locked ## Locked \<longleftrightarrow> (\<bottom>::'a) = \<top>\<close>
  by (force simp add: disjoint_lock_perm.rep_eq Locked_def Unlocked_def Abs_lock_perm_helpers)+

lift_definition plus_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> 'a lock_perm\<close> is \<open>(\<sqinter>)\<close> .

lemma plus_lock_perm_simps[simp]:
  \<open>Locked + Unlocked = Locked\<close>
  \<open>Unlocked + Locked = Locked\<close>
  \<open>Unlocked + Unlocked = Unlocked\<close>
  unfolding Unlocked_def Locked_def
  by (transfer, force)+

instance
  apply standard
          apply (transfer, metis inf.assoc)
         apply (transfer, metis inf.commute)
        apply (transfer, metis sup.commute)
       apply (transfer, simp add: sup_inf_distrib1; fail)
      apply (transfer, simp add: inf_sup_aci(5) sup_inf_distrib1; fail)
     apply (transfer, simp; fail)
    apply (transfer, metis sup_commute sup_inf_absorb)
   apply (transfer, blast)
  apply (transfer, blast)
  done

end

end