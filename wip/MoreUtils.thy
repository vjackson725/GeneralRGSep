theory MoreUtils
  imports "../Util"
begin

unbundle lattice_syntax


context boolean_algebra
begin

definition bequiv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<sim>" 60) where
  "a \<sim> b \<equiv> (a \<leadsto> b) \<sqinter> (b \<leadsto> a)"

lemma bequiv_simps[simp]:
  \<open>a \<sim> a = \<top>\<close>
  \<open>a \<sim> -a = \<bottom>\<close>
  \<open>-a \<sim> a = \<bottom>\<close>
  \<open>a \<sim> \<top> = a\<close>
  \<open>\<top> \<sim> a = a\<close>
  \<open>a \<sim> \<bottom> = -a\<close>
  \<open>\<bottom> \<sim> a = -a\<close>
  by (clarsimp simp add: bequiv_def impl_def)+

lemma bequiv_iff: \<open>a \<sim> b = (-a \<squnion> b) \<sqinter> (-b \<squnion> a)\<close>
  by (simp add: bequiv_def impl_def)

lemma bequiv_iff2: \<open>a \<sim> b = (a \<sqinter> b) \<squnion> (-a \<sqinter> -b)\<close>
  using bequiv_iff sup.commute sup_inf_distrib2 by force

definition bxor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<oplus>" 60) where
  "a \<oplus> b \<equiv> a \<sqinter> -b \<squnion> -a \<sqinter> b"

lemma bxor_simps[simp]:
  \<open>a \<oplus> a = \<bottom>\<close>
  \<open>a \<oplus> -a = \<top>\<close>
  \<open>-a \<oplus> a = \<top>\<close>
  \<open>a \<oplus> \<bottom> = a\<close>
  \<open>\<bottom> \<oplus> a = a\<close>
  \<open>a \<oplus> \<top> = -a\<close>
  \<open>\<top> \<oplus> a = -a\<close>
  by (clarsimp simp add: bxor_def impl_def)+

end

lemma mem_impl_iff[simp]:
  \<open>x \<in> A \<leadsto> B \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)\<close>
  by (simp add: impl_def)

lemma pred_impl_apply[simp]:
  \<open>(a \<leadsto> b) x = (a x \<longrightarrow> b x)\<close>
  by (simp add: impl_def)

lemma rel_impl_apply[simp]:
  \<open>(a \<leadsto> b) x y = (a x y \<longrightarrow> b x y)\<close>
  by (simp add: impl_def)

lemma mem_bequiv_iff[simp]:
  \<open>x \<in> A \<sim> B \<longleftrightarrow> (x \<in> A \<longleftrightarrow> x \<in> B)\<close>
  by (force simp add: bequiv_def)

lemma pred_bequiv_apply[simp]:
  \<open>(a \<sim> b) x \<longleftrightarrow> (a x = b x)\<close>
  by (force simp add: bequiv_def)

lemma rel_bequiv_apply[simp]:
  \<open>(a \<sim> b) x y = (a x y = b x y)\<close>
  by (force simp add: bequiv_def)


end