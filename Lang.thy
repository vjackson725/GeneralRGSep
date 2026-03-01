theory Lang
  imports Util "HOL-Library.Multiset"
begin

section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 's comm =
  Skip
  | Seq \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<^bold>\<sqinter>\<close> 65) \<comment> \<open> note the bold! \<close>
  | Endet \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<^bold>\<box>\<close> 65) \<comment> \<open> note the bold! \<close>
  \<comment> \<open> An atomic action is represented by a relation.
      If the current state is not in the pre-state of the relation,
      the step is blocked. \<close>
  | Atomic \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>\<langle>_\<rangle>\<close> [0] 1000)
  | Iter \<open>'s comm\<close> (\<open>DO _ OD\<close> [0] 999)


subsection \<open> Map atomic commands \<close>

fun map_atom :: \<open>(('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('u \<Rightarrow> 'u \<Rightarrow> bool)) \<Rightarrow> 's comm \<Rightarrow> 'u comm\<close> where
  \<open>map_atom f Skip = Skip\<close>
| \<open>map_atom f (a ;; b) = map_atom f a ;; map_atom f b\<close>
| \<open>map_atom f (a \<parallel> b) = map_atom f a \<parallel> map_atom f b\<close>
| \<open>map_atom f (a \<^bold>\<sqinter> b) = map_atom f a \<^bold>\<sqinter> map_atom f b\<close>
| \<open>map_atom f (a \<^bold>\<box> b) = map_atom f a \<^bold>\<box> map_atom f b\<close>
| \<open>map_atom f (Atomic ar) = Atomic (f ar)\<close>
| \<open>map_atom f (DO a OD) = DO map_atom f a OD\<close>

lemma map_atom_rev_iff:
  \<open>map_atom f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_atom f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<^bold>\<sqinter> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>\<sqinter> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<^bold>\<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>\<box> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_atom f ca)\<close>
  \<open>map_atom f c = Atomic ar' \<longleftrightarrow> (\<exists>ar. ar' = f ar \<and> c = Atomic ar)\<close>
        apply (induct c; (simp add: fun_eq_iff split: prod.splits; argo)+)+
  apply (induct c; force split: prod.splits)
  done

lemmas map_atom_rev_iff2 = map_atom_rev_iff[THEN trans[OF eq_commute]]


lemma map_atom_neq_Skip_iff[simp]:
  \<open>map_atom f c \<noteq> Skip \<longleftrightarrow> c \<noteq> Skip\<close>
  by (induct c) simp+

lemma map_atom_fusion[simp]:
  \<open>map_atom f (map_atom g c) = map_atom (f \<circ> g) c\<close>
  by (induct c) simp+

lemma map_atom_inj_eq_iff_eq:
  \<open>inj f \<Longrightarrow> map_atom f ca = map_atom f cb \<longleftrightarrow> ca = cb\<close>
proof (induct ca arbitrary: cb)
  case (Atomic x)
  then show ?case
    by (clarsimp simp add: map_atom_rev_iff2)
      (metis injD)
qed (simp add: map_atom_rev_iff2; fast)+

lemma map_atom_id_eq[simp]:
  \<open>map_atom id c = c\<close>
  by (induct c) simp+

lemma map_atom_raw_id_eq[simp]:
  \<open>map_atom (\<lambda>x. x) c = c\<close>
  by (metis comp_id fun.map_ident map_atom_id_eq)


subsubsection \<open> Subcommands \<close>

fun subcomms :: \<open>'s comm \<Rightarrow> 's comm multiset\<close> where
  \<open>subcomms Skip = {# Skip #}\<close>
| \<open>subcomms (ca ;; cb) = add_mset (ca ;; cb) (subcomms ca + subcomms cb)\<close>
| \<open>subcomms (ca \<parallel> cb) = add_mset (ca \<parallel> cb) (subcomms ca + subcomms cb)\<close>
| \<open>subcomms (ca \<^bold>\<sqinter> cb) = add_mset (ca \<^bold>\<sqinter> cb) (subcomms ca + subcomms cb)\<close>
| \<open>subcomms (ca \<^bold>\<box> cb) = add_mset (ca \<^bold>\<box> cb) (subcomms ca + subcomms cb)\<close>
| \<open>subcomms \<langle>ar\<rangle> = {# \<langle>ar\<rangle> #}\<close>
| \<open>subcomms (DO c OD) = add_mset (DO c OD) (subcomms c)\<close>


lemma subcomms_size_split:
  \<open>\<exists>A. subcomms c = add_mset c A \<and> (\<forall>c'\<in>#A. size c' < size c)\<close>
  by (induct c) force+

lemma in_subcomms_then_le_size:
  \<open>c' \<in># subcomms c \<Longrightarrow> c' = c \<or> size c' < size c\<close>
  using subcomms_size_split
  by force

lemma subcomms_contains_self[simp]:
  \<open>count (subcomms c) c = 1\<close>
  using subcomms_size_split[of c]
  by (clarsimp, meson count_inI less_not_refl)

lemma subcomms_refl:
  \<open>c \<in># subcomms c\<close>
  by (metis subcomms_size_split union_single_eq_member)

lemma subcomms_trans:
  \<open>x \<in># subcomms y \<Longrightarrow> y \<in># subcomms z \<Longrightarrow> x \<in># subcomms z\<close>
  by (induct z arbitrary: x y) force+

lemma in_subcomms_then_subcomms_subset:
  \<open>y \<in># subcomms x \<Longrightarrow> subcomms y \<subseteq># subcomms x\<close>
  by (induct x arbitrary: y)
    (force intro: subset_mset.trans)+

lemma subcomms_antisym:
  \<open>x \<in># subcomms y \<Longrightarrow> y \<in># subcomms x \<Longrightarrow> x = y\<close>
  apply (frule in_subcomms_then_subcomms_subset[of x])
  apply (frule in_subcomms_then_subcomms_subset[of y])
  apply (metis in_subcomms_then_le_size order_less_asym)
  done


definition \<open>subcomms_strict c = subcomms c - {#c#}\<close>

lemma subcomms[simp]:
  \<open>subcomms_strict Skip = {#}\<close>
  \<open>subcomms_strict (ca ;; cb) = subcomms ca + subcomms cb\<close>
  \<open>subcomms_strict (ca \<parallel> cb) = subcomms ca + subcomms cb\<close>
  \<open>subcomms_strict (ca \<^bold>\<sqinter> cb) = subcomms ca + subcomms cb\<close>
  \<open>subcomms_strict (ca \<^bold>\<box> cb) = subcomms ca + subcomms cb\<close>
  \<open>subcomms_strict \<langle>ar\<rangle> = {#}\<close>
  \<open>subcomms_strict (DO c OD) = subcomms c\<close>
  by (simp add: subcomms_strict_def)+

lemma subcomms_strict_irrefl:
  \<open>c \<notin># subcomms_strict c\<close>
  by (simp add: in_diff_count subcomms_strict_def)

lemma less_comm_less_eq_comm_le_not:
  \<open>(x \<in># subcomms_strict y) = (x \<in># subcomms y \<and> y \<notin># subcomms x)\<close>
  by (metis add_mset_remove_trivial_eq count_add_mset count_greater_zero_iff leD le_eq_less_or_eq
      subcomms_strict_def subcomms_size_split subcomms_strict_irrefl union_single_eq_member)

lemma subcomms_strict_trans:
  \<open>x \<in># subcomms_strict y \<Longrightarrow> y \<in># subcomms_strict z \<Longrightarrow> x \<in># subcomms_strict z\<close>
  unfolding subcomms_strict_def
  by (metis add_mset_remove_trivial_If in_subcomms_then_le_size insert_iff order_less_asym
      set_mset_add_mset_insert subcomms_trans)

lemma subcomms_subcomms_strict_trans:
  \<open>x \<in># subcomms y \<Longrightarrow> y \<in># subcomms_strict z \<Longrightarrow> x \<in># subcomms_strict z\<close>
  by (metis add_mset_diff_bothsides diff_zero insert_iff set_mset_add_mset_insert subcomms_strict_def
      subcomms_size_split subcomms_strict_trans)

lemma subcomms_strict_subcomms_trans:
  \<open>x \<in># subcomms_strict y \<Longrightarrow> y \<in># subcomms z \<Longrightarrow> x \<in># subcomms_strict z\<close>
  by (metis less_comm_less_eq_comm_le_not subcomms_antisym subcomms_strict_trans)

lemma subcomms_strict_no_loops:
  \<open>x \<in># subcomms_strict y \<Longrightarrow> y \<in># subcomms_strict x \<Longrightarrow> False\<close>
  using subcomms_strict_irrefl subcomms_strict_trans by blast


subsubsection \<open> All Subcommands \<close>

definition all_subcomms :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_subcomms f c \<equiv> \<Sqinter>(f ` set_mset (subcomms c))\<close>

lemma all_subcomms_simps[simp]:
  \<open>all_subcomms f Skip = f Skip\<close>
  \<open>all_subcomms f (ca ;; cb) = f (ca ;; cb) \<sqinter> all_subcomms f ca \<sqinter> all_subcomms f cb\<close>
  \<open>all_subcomms f (ca \<parallel> cb) = f (ca \<parallel> cb) \<sqinter> all_subcomms f ca \<sqinter> all_subcomms f cb\<close>
  \<open>all_subcomms f (ca \<^bold>\<sqinter> cb) = f (ca \<^bold>\<sqinter> cb) \<sqinter> all_subcomms f ca \<sqinter> all_subcomms f cb\<close>
  \<open>all_subcomms f (ca \<^bold>\<box> cb) = f (ca \<^bold>\<box> cb) \<sqinter> all_subcomms f ca \<sqinter> all_subcomms f cb\<close>
  \<open>all_subcomms f (DO c OD) = f (DO c OD) \<sqinter> all_subcomms f c\<close>
  \<open>all_subcomms f \<langle>ar\<rangle> = f \<langle>ar\<rangle>\<close>
  by (simp add: all_subcomms_def image_Un Inf_union_distrib inf.assoc)+


subsubsection \<open> Command ordering \<close>

instantiation comm :: (type) order
begin

definition less_eq_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_eq_comm x y \<equiv> x \<in># subcomms y\<close>

definition less_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_comm x y \<equiv> x \<in># subcomms_strict y\<close>

instance
  apply standard
     apply (simp add: less_comm_def less_eq_comm_def less_comm_less_eq_comm_le_not; fail)
    apply (simp add: less_eq_comm_def subcomms_refl; fail)
   apply (simp add: less_eq_comm_def; meson subcomms_trans; fail)
  apply (simp add: less_eq_comm_def; meson subcomms_antisym; fail)
  done

end

lemma less_eq_comm_simps_right[simp]:
  \<open>c \<le> Skip \<longleftrightarrow> c = Skip\<close>
  \<open>c \<le> ca ;; cb \<longleftrightarrow> c = ca ;; cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<parallel> cb \<longleftrightarrow> c = ca \<parallel> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<^bold>\<sqinter> cb \<longleftrightarrow> c = ca \<^bold>\<sqinter> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<^bold>\<box> cb \<longleftrightarrow> c = ca \<^bold>\<box> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> \<langle>ar\<rangle> \<longleftrightarrow> c = \<langle>ar\<rangle>\<close>
  \<open>c \<le> DO cx OD \<longleftrightarrow> c = DO cx OD \<or> c \<le> cx\<close>
  by (simp add: less_eq_comm_def)+

lemma less_comm_simps_right[simp]:
  \<open>c < Skip \<longleftrightarrow> False\<close>
  \<open>c < ca ;; cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<parallel> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<^bold>\<sqinter> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<^bold>\<box> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < \<langle>ar\<rangle> \<longleftrightarrow> False\<close>
  \<open>c < DO cx OD \<longleftrightarrow> c \<le> cx\<close>
  by (simp add: less_comm_def less_eq_comm_def)+

lemma less_eq_comm_leftD:
  \<open>ca ;; cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca ;; cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<parallel> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<parallel> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<^bold>\<sqinter> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<^bold>\<sqinter> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<^bold>\<box> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<^bold>\<box> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>DO cx OD \<le> c \<Longrightarrow> cx \<le> c\<close>
  by (meson order.refl order.trans less_eq_comm_simps_right; fail)+


subsection \<open> Head Commands \<close>

fun head_subcomms :: \<open>'s comm \<Rightarrow> 's comm multiset\<close> where
  \<open>head_subcomms Skip = {# Skip #}\<close>
| \<open>head_subcomms (ca ;; cb) = add_mset (ca ;; cb) (head_subcomms ca)\<close>
| \<open>head_subcomms (ca \<parallel> cb) = add_mset (ca \<parallel> cb) (head_subcomms ca + head_subcomms cb)\<close>
| \<open>head_subcomms (ca \<^bold>\<sqinter> cb) = {# ca \<^bold>\<sqinter> cb #}\<close>
| \<open>head_subcomms (ca \<^bold>\<box> cb) = add_mset (ca \<^bold>\<box> cb) (head_subcomms ca + head_subcomms cb)\<close>
| \<open>head_subcomms \<langle>ar\<rangle> = {# \<langle>ar\<rangle> #}\<close>
| \<open>head_subcomms (DO c OD) = add_mset (DO c OD) (head_subcomms c)\<close>

lemma heads_subcomm_original:
  \<open>\<forall>c'\<in>#head_subcomms c. c' \<in># subcomms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma heads_refl:
  \<open>c \<in># head_subcomms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma head_subcomms_subset_subcomms:
  \<open>head_subcomms c \<subseteq># subcomms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

subsection \<open> all head subcommands \<close>

definition \<open>all_head_subcomms p c \<equiv> \<Sqinter>(p ` set_mset (head_subcomms c))\<close>

lemmas all_head_subcomms_simps[simp] =
  head_subcomms.simps[THEN arg_cong[where f=\<open>\<lambda>x. \<Sqinter>(p ` set_mset x)\<close> for p::\<open>_ \<Rightarrow> _::complete_lattice\<close>],
    simplified all_head_subcomms_def[symmetric],
    simplified, simplified image_Un Inf_union_distrib inf.assoc[symmetric],
    simplified all_head_subcomms_def[symmetric]]

lemma all_subcomms_implies_all_head_subcomms:
  \<open>all_subcomms p c \<le> all_head_subcomms p c\<close>
  unfolding all_subcomms_def all_head_subcomms_def
  using head_subcomms_subset_subcomms
  by (force intro: INF_mono dest: set_mset_mono)


subsection \<open> Atomic Subcommands \<close>

definition
  \<open>subcomm_atoms c \<equiv>
    image_mset (\<lambda>c'. THE a. \<langle>a\<rangle> = c') (filter_mset (\<lambda>c'. \<exists>a. c' = \<langle>a\<rangle>) (subcomms c))\<close>

lemma subcomm_atoms_eq[simp]:
  \<open>subcomm_atoms Skip = {#}\<close>
  \<open>subcomm_atoms (ca ;; cb) = subcomm_atoms ca + subcomm_atoms cb\<close>
  \<open>subcomm_atoms (ca \<parallel> cb) = subcomm_atoms ca + subcomm_atoms cb\<close>
  \<open>subcomm_atoms (ca \<^bold>\<sqinter> cb) = subcomm_atoms ca + subcomm_atoms cb\<close>
  \<open>subcomm_atoms (ca \<^bold>\<box> cb) = subcomm_atoms ca + subcomm_atoms cb\<close>
  \<open>subcomm_atoms \<langle>ar\<rangle> = {# ar #}\<close>
  \<open>subcomm_atoms (DO c OD) = subcomm_atoms c\<close>
  by (force simp add: subcomm_atoms_def)+

lemma set_of_subcomm_atoms_eq[simp]:
  \<open>set_mset (subcomm_atoms c) = {a. \<langle>a\<rangle> \<in># subcomms c}\<close>
  by (fastforce simp add: subcomm_atoms_def image_def set_eq_iff less_eq_comm_def)


subsubsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

definition all_atoms :: \<open>(('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_atoms f c \<equiv> \<Sqinter>{f a|a. a \<in># subcomm_atoms c}\<close>

lemma all_atoms_simps[simp]:
  \<open>all_atoms P Skip = \<top>\<close>
  \<open>all_atoms P (c1 ;; c2) = all_atoms P c1 \<sqinter> all_atoms P c2\<close>
  \<open>all_atoms P (c1 \<^bold>\<sqinter> c2) = all_atoms P c1 \<sqinter> all_atoms P c2\<close>
  \<open>all_atoms P (c1 \<^bold>\<box> c2) = all_atoms P c1 \<sqinter> all_atoms P c2\<close>
  \<open>all_atoms P (c1 \<parallel> c2) = all_atoms P c1 \<sqinter> all_atoms P c2\<close>
  \<open>all_atoms P (DO c OD) = all_atoms P c\<close>
  \<open>all_atoms P (Atomic ar) = P ar\<close>
  by (simp add: all_atoms_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+

lemma all_atoms_pred_mono:
  \<open>P \<le> Q \<Longrightarrow> all_atoms P c \<Longrightarrow> all_atoms Q c\<close>
  unfolding all_atoms_def
  by force

lemma all_atoms_pred_mono':
  \<open>P \<le> Q \<Longrightarrow> all_atoms P \<le> all_atoms Q\<close>
  apply (clarsimp simp add: all_atoms_def le_fun_def)
  apply (rule Inf_mono)
  apply blast
  done

lemmas all_atoms_pred_monoD = all_atoms_pred_mono[rotated]

lemma all_atoms_conj_eq[simp]:
  \<open>all_atoms (P \<sqinter> Q) c \<longleftrightarrow> all_atoms P c \<and> all_atoms Q c\<close>
  unfolding all_atoms_def
  by force

lemma all_atoms_top_eq[simp]:
  \<open>all_atoms \<top> c\<close>
  unfolding all_atoms_def
  by force

lemma all_atoms_then_holds_of_atom:
  \<open>all_atoms p c s \<Longrightarrow>
    r \<in># subcomm_atoms c \<Longrightarrow>
    p r s\<close>
  by (simp add: all_atoms_def) blast


subsection \<open> All Loops \<close>

definition all_loops :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_loops f c \<equiv> \<Sqinter>{f c'|c'. DO c' OD \<in># subcomms c}\<close>

lemma all_loops_simps[simp]:
  \<open>all_loops f Skip = \<top>\<close>
  \<open>all_loops f (c1 ;; c2) = all_loops f c1 \<sqinter> all_loops f c2\<close>
  \<open>all_loops f (c1 \<^bold>\<sqinter> c2) = all_loops f c1 \<sqinter> all_loops f c2\<close>
  \<open>all_loops f (c1 \<^bold>\<box> c2) = all_loops f c1 \<sqinter> all_loops f c2\<close>
  \<open>all_loops f (c1 \<parallel> c2) = all_loops f c1 \<sqinter> all_loops f c2\<close>
  \<open>all_loops f (DO c OD) = f c \<sqinter> all_loops f c\<close>
  \<open>all_loops f (Atomic ar) = \<top>\<close>
  by (simp add: all_loops_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+


subsection \<open> Head Atoms \<close>

definition \<open>head_atoms c \<equiv>
  image_mset (\<lambda>c'. THE a. \<langle>a\<rangle> = c') (filter_mset (\<lambda>c'. \<exists>a. c' = \<langle>a\<rangle>) (head_subcomms c))\<close>

lemmas head_atoms_simps[simp] =
  head_subcomms.simps[
    THEN arg_cong[where f=\<open>\<lambda>x. image_mset (\<lambda>c'. THE a. \<langle>a\<rangle> = c') (filter_mset (\<lambda>c'. \<exists>a. c' = \<langle>a\<rangle>) x)\<close>],
    simplified head_atoms_def[symmetric], simplified,
    simplified head_atoms_def[symmetric]]

lemmas image_mset_head_atoms =
  head_atoms_simps[THEN arg_cong[of _ _ \<open>image_mset _\<close>],
    simplified image_mset_empty image_mset_union,
    of f for f]

lemma head_atoms_subseteq_subcomm_atoms:
  \<open>head_atoms c \<subseteq># subcomm_atoms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma head_atoms_eq_atoms_of_heads:
  \<open>head_atoms c =
    image_mset (\<lambda>c'. THE ar. c' = \<langle>ar\<rangle>)
      (filter_mset (\<lambda>c'. \<exists>ar. c' = \<langle>ar\<rangle>)
        (head_subcomms c))\<close>
  by (induct c) simp+

lemma all_atoms_then_holds_of_head_atom:
  \<open>all_atoms p c s \<Longrightarrow>
    r \<in># head_atoms c \<Longrightarrow>
    p r s\<close>
  by (metis all_atoms_then_holds_of_atom head_atoms_subseteq_subcomm_atoms mset_subset_eqD)


subsubsection \<open> All Head Atoms \<close>

definition \<open>all_head_atoms p c \<equiv> \<Sqinter>(p ` set_mset (head_atoms c))\<close>

lemmas all_head_atoms_simps[simp] =
  head_atoms_simps[THEN arg_cong[where f=\<open>\<lambda>x. \<Sqinter>(p ` set_mset x)\<close> for p::\<open>_ \<Rightarrow> _::complete_lattice\<close>],
    simplified all_head_atoms_def[symmetric],
    simplified, simplified image_Un Inf_union_distrib,
    simplified all_head_atoms_def[symmetric]]

lemma all_atoms_implies_all_head_atoms:
  \<open>all_atoms f c \<le> all_head_atoms f c\<close>
  using head_atoms_subseteq_subcomm_atoms
  apply (simp add: all_atoms_def all_head_atoms_def)
  apply (rule Inf_mono)
  apply (fastforce dest: mset_subset_eqD)
  done

lemma all_head_atoms_then_holds_of_head_atom:
  \<open>all_head_atoms p c \<Longrightarrow>
    r \<in># head_atoms c \<Longrightarrow>
    p r\<close>
  by (simp add: all_head_atoms_def)


subsection \<open> Any Head Atom \<close>

definition
  \<open>any_head_atom (p :: _ \<Rightarrow> 'l::complete_lattice) c \<equiv>
    \<Squnion>(p ` set_mset (head_atoms c))\<close>

lemmas any_head_atom_simps[simp] =
  head_atoms_simps[THEN arg_cong[where f=\<open>\<lambda>x. \<Squnion>(p ` set_mset x)\<close> for p::\<open>_ \<Rightarrow> _::complete_lattice\<close>],
    simplified any_head_atom_def[symmetric],
    simplified, simplified image_Un Sup_union_distrib,
    simplified any_head_atom_def[symmetric]]


subsection \<open> All Head Loops \<close>

definition all_head_loops :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_head_loops f c \<equiv> \<Sqinter>{f c'|c'. DO c' OD \<in># head_subcomms c}\<close>

lemma all_head_loops_simps[simp]:
  \<open>all_head_loops f Skip = \<top>\<close>
  \<open>all_head_loops f (c1 ;; c2) = all_head_loops f c1\<close>
  \<open>all_head_loops f (c1 \<^bold>\<sqinter> c2) = \<top>\<close>
  \<open>all_head_loops f (c1 \<^bold>\<box> c2) = all_head_loops f c1 \<sqinter> all_head_loops f c2\<close>
  \<open>all_head_loops f (c1 \<parallel> c2) = all_head_loops f c1 \<sqinter> all_head_loops f c2\<close>
  \<open>all_head_loops f (DO c OD) = f c \<sqinter> all_head_loops f c\<close>
  \<open>all_head_loops f (Atomic ar) = \<top>\<close>
  by (simp add: all_head_loops_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+

lemma all_loops_implies_all_head_loops:
  \<open>all_loops f c \<le> all_head_loops f c\<close>
  apply (simp add: all_loops_def all_head_loops_def)
  apply (rule Inf_mono)
  apply clarsimp
  apply (metis order.refl heads_subcomm_original less_eq_comm_def)
  done


subsection \<open> Atom Headed \<close>

text \<open>
  A syntactic check for stability (inability to make tau moves) on every state.

  A predicate to determine if the directly executed subcommand is an atom.
  (As opposed to a command like \<open>Skip; c\<close>.)
  Note that a do-loop is also an executable head,
  as when the loop's subcommand is blocked, it can reduce itself.
\<close>
fun head_atomic where
  \<open>head_atomic Skip = True\<close>
| \<open>head_atomic (ca ;; cb) = (ca \<noteq> Skip \<and> head_atomic ca)\<close>
| \<open>head_atomic (ca \<parallel> cb) = ((ca \<noteq> Skip \<or> cb \<noteq> Skip) \<and> head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic (ca \<^bold>\<box> cb) = ((ca \<noteq> Skip \<and> cb \<noteq> Skip) \<and> head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic (ca \<^bold>\<sqinter> cb) = False\<close>
| \<open>head_atomic \<langle>ar\<rangle> = True\<close>
| \<open>head_atomic (DO c OD) = (All (any_head_atom pre_state c) \<and> head_atomic c)\<close>


section \<open> Specific Commands \<close>

subsection \<open> Await \<close>

definition \<open>await_rel p \<equiv> pretest p \<sqinter> (=)\<close>
abbreviation \<open>Await p \<equiv> Atomic (await_rel p)\<close>

lemma await_rel_inject[simp]:
  \<open>await_rel p1 = await_rel p2 \<longleftrightarrow> p1 = p2\<close>
  by (force simp add: await_rel_def fun_eq_iff pretest_def)

lemma sp_await_rel[simp]:
  \<open>sp (await_rel p) = (\<sqinter>) p\<close>
  by (force simp add: sp_def await_rel_def)

subsection \<open> If-then-else \<close>

definition \<open>IfThenElse p ct cf \<equiv> Await p ;; ct \<^bold>\<box> Await (-p) ;; cf\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: IfThenElse_def)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> \<langle>ar\<rangle>\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>\<langle>ar\<rangle> \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+


subsection \<open> WhileLoop \<close>

definition \<open>WhileLoop p c \<equiv> DO (Await p ;; c) OD\<close>

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def await_rel_def fun_eq_iff, blast)

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<^bold>\<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> \<langle>ar\<rangle>\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<^bold>\<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>\<langle>ar\<rangle> \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def; fail)+


end