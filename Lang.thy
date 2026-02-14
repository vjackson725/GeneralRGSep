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

subsection \<open> substitution \<close>

subsection \<open> All Sub-commands \<close>

fun all_subcomm_eq :: \<open>'s comm \<Rightarrow> 's comm set\<close> where
  \<open>all_subcomm_eq Skip = {Skip}\<close>
| \<open>all_subcomm_eq (ca ;; cb) =
    insert (ca ;; cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<parallel> cb) =
    insert (ca \<parallel> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<^bold>\<sqinter> cb) =
    insert (ca \<^bold>\<sqinter> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<^bold>\<box> cb) =
    insert (ca \<^bold>\<box> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq \<langle>ar\<rangle> = {\<langle>ar\<rangle>}\<close>
| \<open>all_subcomm_eq (DO c OD) = insert (DO c OD) (all_subcomm_eq c)\<close>

fun all_subcomm :: \<open>'s comm \<Rightarrow> 's comm set\<close> where
  \<open>all_subcomm Skip = {}\<close>
| \<open>all_subcomm (ca ;; cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<parallel> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<^bold>\<sqinter> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<^bold>\<box> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm \<langle>ar\<rangle> = {}\<close>
| \<open>all_subcomm (DO c OD) = (all_subcomm_eq c)\<close>


lemma all_subcomm_eq_eq:
  \<open>all_subcomm_eq c = insert c (all_subcomm c)\<close>
  by (induct c) force+

lemma all_subcomm_eq_trans:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm_eq z \<Longrightarrow> x \<in> all_subcomm_eq z\<close>
  by (induct z arbitrary: x y) force+

lemma all_subcomm_trans:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (simp; metis all_subcomm_eq_eq insert_iff)+

lemma all_subcomm_all_subcomm_eq_trans:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm_eq z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (fastforce simp add: all_subcomm_eq_eq)+

lemma all_subcomm_eq_all_subcomm_trans:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (fastforce simp add: all_subcomm_eq_eq)+

lemma all_subcomm_irrefl:
  \<open>x \<notin> all_subcomm x\<close>
  apply (induct x)
        apply force
       apply (simp, metis UnCI all_subcomm.simps(2)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
      apply (simp, metis UnCI all_subcomm.simps(3)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
     apply (simp, metis UnCI all_subcomm.simps(4)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
    apply (simp, metis UnCI all_subcomm.simps(5)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
   apply force
  apply (simp, metis all_subcomm.simps(7)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
  done

lemma in_all_subcomm_iff_in_allsubcomm_eq_neq:
  \<open>(x \<in> all_subcomm y) = (x \<in> all_subcomm_eq y \<and> x \<noteq> y)\<close>
  using all_subcomm_eq_eq all_subcomm_irrefl by blast

lemma all_subcomm_eq_loop_then_eq:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm_eq x \<Longrightarrow> x = y\<close>
  apply (induct y arbitrary: x)
        apply force
       apply (simp, metis UnCI all_subcomm.simps(2) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
      apply (simp, metis UnCI all_subcomm.simps(3) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
     apply (simp, metis UnCI all_subcomm.simps(4) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
    apply (simp, metis UnCI all_subcomm.simps(5) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
   apply force
  apply (simp, metis all_subcomm.simps(7) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
  done

lemma all_subcomm_no_loops:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm x \<Longrightarrow> False\<close>
  using all_subcomm_irrefl all_subcomm_trans by blast


subsubsection \<open> All Subcommands Conjunctive Image \<close>

definition all_subcomm_eq_InfIm :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_subcomm_eq_InfIm f c \<equiv> \<Sqinter>(f ` all_subcomm_eq c)\<close>

lemma all_subcomm_eq_InfIm_simps[simp]:
  \<open>all_subcomm_eq_InfIm f Skip = f Skip\<close>
  \<open>all_subcomm_eq_InfIm f (ca ;; cb) = f (ca ;; cb) \<sqinter> all_subcomm_eq_InfIm f ca \<sqinter> all_subcomm_eq_InfIm f cb\<close>
  \<open>all_subcomm_eq_InfIm f (ca \<parallel> cb) = f (ca \<parallel> cb) \<sqinter> all_subcomm_eq_InfIm f ca \<sqinter> all_subcomm_eq_InfIm f cb\<close>
  \<open>all_subcomm_eq_InfIm f (ca \<^bold>\<sqinter> cb) = f (ca \<^bold>\<sqinter> cb) \<sqinter> all_subcomm_eq_InfIm f ca \<sqinter> all_subcomm_eq_InfIm f cb\<close>
  \<open>all_subcomm_eq_InfIm f (ca \<^bold>\<box> cb) = f (ca \<^bold>\<box> cb) \<sqinter> all_subcomm_eq_InfIm f ca \<sqinter> all_subcomm_eq_InfIm f cb\<close>
  \<open>all_subcomm_eq_InfIm f (DO c OD) = f (DO c OD) \<sqinter> all_subcomm_eq_InfIm f c\<close>
  \<open>all_subcomm_eq_InfIm f \<langle>ar\<rangle> = f \<langle>ar\<rangle>\<close>
  by (simp add: all_subcomm_eq_InfIm_def image_Un Inf_union_distrib inf.assoc)+


subsubsection \<open> Command ordering \<close>

instantiation comm :: (type) order
begin

definition less_eq_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_eq_comm x y \<equiv> x \<in> all_subcomm_eq y\<close>

definition less_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_comm x y \<equiv> x \<in> all_subcomm y\<close>

lemma less_comm_less_eq_comm_le_not:
  \<open>(x \<in> all_subcomm y) = (x \<in> all_subcomm_eq y \<and> y \<notin> all_subcomm_eq x)\<close>
  using all_subcomm_eq_all_subcomm_trans in_all_subcomm_iff_in_allsubcomm_eq_neq
  by blast

instance
  apply standard
     apply (simp add: less_comm_def less_comm_less_eq_comm_le_not
      less_eq_comm_def; fail)
    apply (simp add: all_subcomm_eq_eq less_eq_comm_def; fail)
   apply (simp add: less_eq_comm_def, metis all_subcomm_eq_trans)
  apply (simp add: less_eq_comm_def all_subcomm_eq_loop_then_eq; fail)
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


subsection \<open> Atoms \<close>

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

lemma map_atom_fusion[simp]:
  \<open>map_atom f (map_atom g c) = map_atom (f \<circ> g) c\<close>
  by (induct c) simp+


fun all_atoms :: \<open>'s comm \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) multiset\<close> where
  \<open>all_atoms Skip = {#}\<close>
| \<open>all_atoms (ca ;; cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<parallel> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<^bold>\<sqinter> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<^bold>\<box> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms \<langle>ar\<rangle> = {# ar #}\<close>
| \<open>all_atoms (DO c OD) = all_atoms c\<close>


subsubsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

definition all_atom_comm :: \<open>(('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_atom_comm f c \<equiv> \<Sqinter>{f ar| ar. ar \<in># all_atoms c}\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm P Skip = \<top>\<close>
  \<open>all_atom_comm P (c1 ;; c2) = all_atom_comm P c1 \<sqinter> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<^bold>\<sqinter> c2) = all_atom_comm P c1 \<sqinter> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<^bold>\<box> c2) = all_atom_comm P c1 \<sqinter> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<parallel> c2) = all_atom_comm P c1 \<sqinter> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (DO c OD) = all_atom_comm P c\<close>
  \<open>all_atom_comm P (Atomic ar) = P ar\<close>
  by (simp add: all_atom_comm_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+

lemma all_atom_comm_pred_mono:
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P c \<Longrightarrow> all_atom_comm Q c\<close>
  unfolding all_atom_comm_def
  by force

lemma all_atom_comm_pred_mono':
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P \<le> all_atom_comm Q\<close>
  apply (clarsimp simp add: all_atom_comm_def le_fun_def)
  apply (rule Inf_mono)
  apply blast
  done

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq[simp]:
  \<open>all_atom_comm (P \<sqinter> Q) c \<longleftrightarrow> all_atom_comm P c \<and> all_atom_comm Q c\<close>
  unfolding all_atom_comm_def
  by force

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  unfolding all_atom_comm_def
  by force


subsection \<open> All Loops \<close>

definition all_loop_comm :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_loop_comm f c \<equiv> \<Sqinter>{f c'|c'. (DO c' OD) \<le> c}\<close>

lemma all_loop_comm_simps[simp]:
  \<open>all_loop_comm f Skip = \<top>\<close>
  \<open>all_loop_comm f (c1 ;; c2) = all_loop_comm f c1 \<sqinter> all_loop_comm f c2\<close>
  \<open>all_loop_comm f (c1 \<^bold>\<sqinter> c2) = all_loop_comm f c1 \<sqinter> all_loop_comm f c2\<close>
  \<open>all_loop_comm f (c1 \<^bold>\<box> c2) = all_loop_comm f c1 \<sqinter> all_loop_comm f c2\<close>
  \<open>all_loop_comm f (c1 \<parallel> c2) = all_loop_comm f c1 \<sqinter> all_loop_comm f c2\<close>
  \<open>all_loop_comm f (DO c OD) = f c \<sqinter> all_loop_comm f c\<close>
  \<open>all_loop_comm f (Atomic ar) = \<top>\<close>
  by (simp add: all_loop_comm_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+


subsection \<open> Head Commands \<close>

subsubsection \<open> Head Commands Definition \<close>

fun head_comms :: \<open>'s comm \<Rightarrow> 's comm multiset\<close> where
  \<open>head_comms Skip = {# Skip #}\<close>
| \<open>head_comms (ca ;; cb) = add_mset (ca ;; cb) (head_comms ca)\<close>
| \<open>head_comms (ca \<parallel> cb) = add_mset (ca \<parallel> cb) (head_comms ca + head_comms cb)\<close>
| \<open>head_comms (ca \<^bold>\<sqinter> cb) = {# ca \<^bold>\<sqinter> cb #}\<close>
| \<open>head_comms (ca \<^bold>\<box> cb) = add_mset (ca \<^bold>\<box> cb) (head_comms ca + head_comms cb)\<close>
| \<open>head_comms \<langle>ar\<rangle> = {# \<langle>ar\<rangle> #}\<close>
| \<open>head_comms (DO c OD) = add_mset (DO c OD) (head_comms c)\<close>

lemma heads_subcomm_original:
  \<open>\<forall>c'\<in>#head_comms c. c' \<le> c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma heads_refl:
  \<open>c \<in># head_comms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma head_comms_subset_all_subcomm_eq:
  \<open>set_mset (head_comms c) \<le> all_subcomm_eq c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+


subsubsection \<open> All Head Commands \<close>

definition all_head_comm :: \<open>('s comm \<Rightarrow> 'l::complete_lattice) \<Rightarrow>'s comm \<Rightarrow> 'l\<close> where
  \<open>all_head_comm f c \<equiv> \<Sqinter>{f c'|c'. c' \<in># head_comms c}\<close>

lemma all_head_comm_simps[simp]:
  \<open>all_head_comm f Skip = f Skip\<close>
  \<open>all_head_comm f (ca ;; cb) = f (ca ;; cb) \<sqinter> all_head_comm f ca\<close>
  \<open>all_head_comm f (ca \<^bold>\<sqinter> cb) = f (ca \<^bold>\<sqinter> cb)\<close>
  \<open>all_head_comm f (ca \<^bold>\<box> cb) = f (ca \<^bold>\<box> cb) \<sqinter> all_head_comm f ca \<sqinter> all_head_comm f cb\<close>
  \<open>all_head_comm f (ca \<parallel> cb) = f (ca \<parallel> cb) \<sqinter> all_head_comm f ca \<sqinter> all_head_comm f cb\<close>
  \<open>all_head_comm f (DO c OD) = f (DO c OD) \<sqinter> all_head_comm f c\<close>
  \<open>all_head_comm f \<langle>ra\<rangle> = f \<langle>ra\<rangle>\<close>
  by (clarsimp simp add: all_head_comm_def conj_disj_distribL ex_disj_distrib Collect_disj_eq
      Inf_union_distrib inf_assoc)+

lemma all_head_comm_le_all_subcomm_eq:
  \<open>all_subcomm_eq_InfIm f c \<le> all_head_comm f c\<close>
  unfolding all_head_comm_def all_subcomm_eq_InfIm_def
  using head_comms_subset_all_subcomm_eq
  by (blast intro: Inf_mono)


subsection \<open> Head Atoms \<close>

fun head_atoms :: \<open>'s comm \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) multiset\<close> where
  \<open>head_atoms Skip = {#}\<close>
| \<open>head_atoms (ca ;; cb) = head_atoms ca\<close>
| \<open>head_atoms (ca \<parallel> cb) = (head_atoms ca + head_atoms cb)\<close>
| \<open>head_atoms (ca \<^bold>\<sqinter> cb) = {#}\<close>
| \<open>head_atoms (ca \<^bold>\<box> cb) = (head_atoms ca + head_atoms cb)\<close>
| \<open>head_atoms \<langle>ar\<rangle> = {# ar #}\<close>
| \<open>head_atoms (DO c OD) = head_atoms c\<close>

lemma head_atoms_subseteq_all_atoms:
  \<open>head_atoms c \<subseteq># all_atoms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+

lemma head_atoms_eq_atoms_of_heads:
  \<open>head_atoms c =
    image_mset (\<lambda>c'. THE ar. c' = \<langle>ar\<rangle>)
      (filter_mset (\<lambda>c'. \<exists>ar. c' = \<langle>ar\<rangle>)
        (head_comms c))\<close>
  by (induct c) simp+


subsubsection \<open> All Head Atoms \<close>

definition all_head_atoms :: \<open>(('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'l::complete_lattice) \<Rightarrow> 's comm \<Rightarrow> 'l\<close> where
  \<open>all_head_atoms f c \<equiv> \<Sqinter>{f c'|c'. c' \<in># head_atoms c}\<close>

lemma all_head_atoms_simps[simp]:
  \<open>all_head_atoms f Skip = \<top>\<close>
  \<open>all_head_atoms f (c1 ;; c2) = all_head_atoms f c1\<close>
  \<open>all_head_atoms f (c1 \<^bold>\<sqinter> c2) = \<top>\<close>
  \<open>all_head_atoms f (c1 \<^bold>\<box> c2) = all_head_atoms f c1 \<sqinter> all_head_atoms f c2\<close>
  \<open>all_head_atoms f (c1 \<parallel> c2) = all_head_atoms f c1 \<sqinter> all_head_atoms f c2\<close>
  \<open>all_head_atoms f (DO c OD) = all_head_atoms f c\<close>
  \<open>all_head_atoms f (Atomic ar) =  f ar\<close>
  by (simp add: all_head_atoms_def all_conj_distrib conj_disj_distribL ex_disj_distrib
      Collect_disj_eq Inf_union_distrib; fail)+


subsection \<open> Atom Headed \<close>

text \<open>
  A predicate to determine if every executable subcommand in this command is an atom.
  (As opposed to a command like \<open>Skip; c\<close>.) Note that a do-loop is also a head,
  as when the loop's subcommand is blocked, it can reduce itself.

  Note that this is not just an application of \<open>all_head_comm\<close> as that includes all programs
  that contain the 'principal' heads containing.
\<close>
fun head_atomic :: \<open>'s comm \<Rightarrow> bool\<close> where
  \<open>head_atomic Skip = False\<close>
| \<open>head_atomic (ca ;; cb) = head_atomic ca\<close>
| \<open>head_atomic (ca \<parallel> cb) = (head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic (ca \<^bold>\<sqinter> cb) = False\<close>
| \<open>head_atomic (ca \<^bold>\<box> cb) = (head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic \<langle>ar\<rangle> = True\<close>
| \<open>head_atomic (DO c OD) = False\<close>


section \<open> Specific Commands \<close>

subsection \<open> Await \<close>


definition \<open>await_rel p \<equiv> rel_liftL p \<sqinter> (=)\<close>
abbreviation \<open>Await p \<equiv> Atomic (await_rel p)\<close>

lemma await_rel_inject[simp]:
  \<open>await_rel p1 = await_rel p2 \<longleftrightarrow> p1 = p2\<close>
  by (force simp add: await_rel_def fun_eq_iff rel_lift_def)

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