theory Lang
  imports SepAlgInstances "HOL-Library.Multiset"
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


section \<open> Specific Languages \<close>

(* TODO: move *)

subsection \<open> Failure State \<close>

datatype fail_st = Running | Failed

lemma all_fail_st_eq:
  \<open>All P \<longleftrightarrow> P Running \<and> P Failed\<close>
  by (metis (full_types) fail_st.exhaust)

lemma ex_fail_st_eq:
  \<open>Ex P \<longleftrightarrow> P Running \<or> P Failed\<close>
  by (metis (full_types) fail_st.exhaust)


subsubsection \<open> Instances \<close>

\<comment> \<open>
  This is similar to the distributive lattice separation algebra,
  except that addition is always allowed. This fact makes the algebra non-cancellative.
\<close>

paragraph \<open> Order \<close>

instantiation fail_st :: ord
begin
definition \<open>less_eq_fail_st a b \<equiv> a = b \<or> b = Failed\<close>
definition \<open>less_fail_st a b \<equiv> a = Running \<and> b = Failed\<close>
instance by standard
end

lemma less_eq_fail_st_iff[simp]:
  \<open>Running \<le> b\<close>
  \<open>a \<le> Failed\<close>
  \<open>Failed \<le> b \<longleftrightarrow> b = Failed\<close>
  \<open>a \<le> Running \<longleftrightarrow> a = Running\<close>
  unfolding less_eq_fail_st_def
  by (cut_tac fail_st.nchotomy; metis (full_types))+

lemma less_fail_st_iff[simp]:
  \<open>Running < b \<longleftrightarrow> b = Failed\<close>
  \<open>a < Failed \<longleftrightarrow> a = Running\<close>
  \<open>Failed < b \<longleftrightarrow> False\<close>
  \<open>a < Running \<longleftrightarrow> False\<close>
  unfolding less_fail_st_def
  by (cut_tac fail_st.nchotomy fail_st.simps; metis (full_types))+

instance fail_st :: order
  apply standard
     apply (case_tac x; case_tac y; simp; fail)
    apply (case_tac x; simp; fail)
   apply (case_tac z; simp; fail)
  apply (case_tac x; case_tac y; simp; fail)
  done


paragraph \<open> Sup \<close>

instantiation fail_st :: sup
begin
definition \<open>sup_fail_st a b \<equiv> if a = Failed \<or> b = Failed then Failed else Running\<close>
instance by standard
end

lemma sup_fail_st_eq[simp]:
  \<open>a \<squnion> Running = a\<close>
  \<open>Running \<squnion> b = b\<close>
  \<open>a \<squnion> Failed = Failed\<close>
  \<open>Failed \<squnion> b = Failed\<close>
  unfolding sup_fail_st_def
  by (cut_tac fail_st.nchotomy; metis (full_types))+

instance fail_st :: semilattice_sup
  by standard (case_tac x; simp; fail)+


paragraph \<open> Inf \<close>

instantiation fail_st :: inf
begin
definition \<open>inf_fail_st a b \<equiv> if a = Running \<or> b = Running then Running else Failed\<close>
instance by standard
end

lemma inf_fail_st_eq[simp]:
  \<open>a \<sqinter> Running = Running\<close>
  \<open>Running \<sqinter> b = Running\<close>
  \<open>a \<sqinter> Failed = a\<close>
  \<open>Failed \<sqinter> b = b\<close>
  unfolding inf_fail_st_def
  by (cut_tac fail_st.nchotomy; metis)+

instance fail_st :: semilattice_inf
  by standard (case_tac x; simp; fail)+

paragraph \<open> Bounds \<close>

instantiation fail_st :: top
begin
definition \<open>top_fail_st \<equiv> Failed\<close>
instance by standard
end

instantiation fail_st :: bot
begin
definition \<open>bot_fail_st \<equiv> Running\<close>
instance by standard
end

instance fail_st :: order_top
  by standard (case_tac a; simp add: top_fail_st_def)

instance fail_st :: order_bot
  by standard (case_tac a; simp add: bot_fail_st_def)


paragraph \<open> Lattice \<close>

\<comment> \<open> automatically a \<open>lattice\<close> \<close>
\<comment> \<open> automatically a \<open>bounded_lattice\<close> \<close>
instance fail_st :: distrib_lattice
  by standard (case_tac x; simp)

paragraph \<open> Boolean Algebra \<close>

instantiation fail_st :: uminus
begin
definition \<open>uminus_fail_st a \<equiv> if a = Running then Failed else Running\<close>
instance by standard
end

lemma uminus_fail_st_eq[simp]:
  \<open>- Running = Failed\<close>
  \<open>- Failed = Running\<close>
  unfolding uminus_fail_st_def
  by metis+

instantiation fail_st :: minus
begin
definition \<open>minus_fail_st (a::fail_st) b \<equiv> a \<sqinter> - b\<close>
instance by standard
end

lemma minus_fail_st_eq[simp]:
  \<open>Running - a = Running\<close>
  \<open>Failed - a = - a\<close>
  \<open>a - Running = a\<close>
  \<open>a - Failed = Running\<close>
  unfolding minus_fail_st_def
  by (case_tac a; simp)+

instance fail_st :: boolean_algebra
  by standard
    (case_tac x; simp add: bot_fail_st_def top_fail_st_def)+


paragraph \<open> Separation Logic \<close>

instantiation fail_st :: plus
begin
definition \<open>plus_fail_st \<equiv> (\<squnion>) :: fail_st \<Rightarrow> _ \<Rightarrow> _\<close>
instance by standard
end

instantiation fail_st :: disjoint
begin
definition \<open>disjoint_fail_st (a::fail_st) (b::fail_st) \<equiv> True\<close>
instance by standard
end

lemma fail_st_disjoint_eq[simp]:
  \<open>(a::fail_st) ## (b::fail_st)\<close>
  unfolding disjoint_fail_st_def ..

instance fail_st :: pre_perm_alg
  apply standard
      apply (simp add: plus_fail_st_def, metis sup.assoc)
     apply (simp add: plus_fail_st_def, metis sup.commute)
    apply (simp add: plus_fail_st_def)+
  done

(* TODO: move *)
lemma (in semilattice_inf) inf_antisym:
  \<open>a \<sqinter> cx = b \<Longrightarrow> b \<sqinter> cy = a \<Longrightarrow> a = b\<close>
  by (metis inf.left_idem inf.commute)

lemma (in semilattice_sup) sup_antisym:
  \<open>a \<squnion> cx = b \<Longrightarrow> b \<squnion> cy = a \<Longrightarrow> a = b\<close>
  by (metis sup.right_idem sup.commute)


instance fail_st :: perm_alg
  by standard (force simp add: plus_fail_st_def dest: sup_antisym)

instantiation fail_st :: multiunit_sep_alg
begin
definition \<open>unitof_fail_st (_::fail_st) \<equiv> Running\<close>
instance
  by standard (simp add: unitof_fail_st_def plus_fail_st_def)+
end

instantiation fail_st :: zero
begin
definition \<open>zero_fail_st \<equiv> Running\<close>
instance by standard
end

instance fail_st :: sep_alg
  by standard (simp add: zero_fail_st_def plus_fail_st_def)+


subsubsection \<open> Await \<close>

definition \<open>Await p \<equiv> Atomic (rel_liftL p \<sqinter> (=))\<close>

lemma Await_inject[simp]:
  \<open>Await p1 = Await p2 \<longleftrightarrow> p1 = p2\<close>
  by (force simp add: Await_def fun_eq_iff rel_lift_def)

subsection \<open> If-then-else \<close>

definition \<open>IfThenElse p ct cf \<equiv> Await p ;; ct \<^bold>\<box> Await (-p) ;; cf\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: IfThenElse_def fun_eq_iff)

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
  by (simp add: WhileLoop_def Await_def fun_eq_iff, blast)

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


section \<open> Logic Utils \<close>


section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

lemmas relyrel_trans = rel_times_trans[OF transp_equality transp_rtranclp]
lemmas relyrel_mono = rel_times_mono[OF order.refl rtranclp_mono]


subsection \<open> step properties \<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sswa_step:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemmas sswa_stepD = sswa_step[rotated]

lemma wssa_step:
  \<open>r y y' \<Longrightarrow>
    wssa r p (x, y) \<Longrightarrow>
    wssa r p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)

lemmas wssa_stepD = wssa_step[rotated]

subsection \<open> closure operator properties \<close>

lemmas sswa_weaker = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_trivial[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

lemmas sswa_rel_mono = sp_rel_mono[OF relyrel_mono]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (drule wlp_refl_relD[rotated], simp)

lemmas wssa_stronger = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_rel_antimono = wlp_rel_antimono[OF relyrel_mono]

lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_stronger_strengthen =
  transp_wlp_stronger_strengthen[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified,
    OF _ relyrel_trans]

lemma sswa_bot_rel_eq[simp]:
  \<open>sswa \<bottom> p = p\<close>
  by (clarsimp simp add: sp_def fun_eq_iff)
    (metis (full_types) rtranclp_eq_eq rtranclp_reflclp sup_bot_left)

lemma wssa_bot_rel_eq[simp]:
  \<open>wssa \<bottom> p = p\<close>
  by (clarsimp simp add: wlp_def fun_eq_iff)
    (metis (full_types) rtranclp_eq_eq rtranclp_reflclp sup_bot_left)


subsection \<open> absorption/pseduo-idempotence properties \<close>

(*
lemmas sswa_idem[simp] =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_idem[simp] =
  wlp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
*)

lemma sswa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1) sp_relcomp)

lemma wssa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (wssa r2 p) = wssa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2) wlp_relcomp)

lemma sswa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (wssa r2 p) = wssa r2 p\<close>
  by (force simp add: relyrel_trans relyrel_mono sp_wlp_absorb)

lemma wssa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: relyrel_mono relyrel_trans wlp_sp_absorb)


subsection \<open> semi-distributivity with sepconj-conj \<close>

lemma wlp_rely_sepconj_conj_semidistrib_mono:
  \<open>p' \<le> wlp ((=) \<times>\<^sub>R r) p \<Longrightarrow>
    q' \<le> wlp ((=) \<times>\<^sub>R r) q \<Longrightarrow>
    p' \<^emph>\<and> q' \<le> wlp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q)\<close>
  by (fastforce simp add: wlp_def sepconj_conj_def le_fun_def)

lemmas wlp_rely_sepconj_conj_semidistrib =
  wlp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma sp_rely_sepconj_conj_semidistrib_mono:
  \<open>sp ((=) \<times>\<^sub>R r) p \<le> p' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) q \<le> q' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q) \<le> p' \<^emph>\<and> q'\<close>
  by (fastforce simp add: sp_def sepconj_conj_def le_fun_def)

lemmas sp_rely_sepconj_conj_semidistrib =
  sp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

subsection \<open> Interaction with pred-Times \<close>

lemma wssa_of_pred_Times_eq[simp]:
  \<open>wssa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_times_def pred_times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_times_def pred_times_def sp_def split: prod.splits)


subsection \<open> Local and shared predicate lifting \<close>

abbreviation(input) local_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S>(p) \<equiv> p \<circ> snd\<close>

lemma wssa_ignore_local[simp]:
  \<open>wssa r (\<L> pl) = \<L> pl\<close>
  by (fastforce simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_ignore_local[simp]:
  \<open>sswa r (\<L> pl) = \<L> pl\<close>
  \<open>sswa r (\<L> pl \<^emph>\<and> q) = \<L> pl \<^emph>\<and> sswa r q\<close>
  \<open>sswa r (p \<^emph>\<and> \<L> ql) = sswa r p \<^emph>\<and> \<L> ql\<close>
  \<open>sswa r (\<L> pl \<sqinter> q) = \<L> pl \<sqinter> sswa r q\<close>
  \<open>sswa r (p \<sqinter> \<L> ql) = sswa r p \<sqinter> \<L> ql\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)+

lemma wssa_over_shared:
  \<open>wssa r (\<S> ps) = \<S> (wlp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_over_shared:
  \<open>sswa r (\<S> ps) = \<S> (sp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)

lemma wssa_semiignore_local:
  \<open>\<L> pl \<^emph>\<and> wssa r q \<le> wssa r (\<L> pl \<^emph>\<and> q)\<close>
  \<open>wssa r p \<^emph>\<and> \<L> ql \<le> wssa r (p \<^emph>\<and> \<L> ql)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)+

text \<open>
  The full law local ignore law is _not_ true for \<open>wssa\<close>, unlike the one for \<open>sswa\<close>.
  Imagine the following situation:
    State model: \<open>bool \<times> bool\<close>
    Sep-algebra: \<open>R000, R011, R101, R111\<close>
    Inputs:
      \<open>q = {11, 00}\<close>
      \<open>r = (0 \<leadsto> 1, 0 \<leadsto> 1)\<close>
    Results:
      \<open>wssa r q = {}\<close>
      \<open>\<L> \<top> \<^emph>\<and> q = {11, 10, 00}\<close>
      \<open>(\<L> pl \<^emph>\<and> wssa r q) = {}\<close>
      \<open>wssa r (\<L> pl \<^emph>\<and> q) = {11, 10}\<close>
    Here we observe that the outputs are not the same, because \<open>wssa\<close> only preserves
    a \<^emph>\<open>subset\<close> of the initial predicate, and this subset might not be compatible
    with the frame.
\<close>
lemma sepconj_local_eq:
  \<open>\<L> p \<^emph>\<and> \<L> q = \<L> (p \<^emph> q)\<close>
  by (simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma sepconj_shared_eq:
  \<open>(\<S> p :: 'a::multiunit_sep_alg \<times> 'b \<Rightarrow> bool) \<^emph>\<and> \<S> q = \<S> (p \<sqinter> q)\<close>
  by (force simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma shared_sepconj_conj_eq:
  \<open>(\<S> p \<^emph>\<and> q) = \<S> p \<sqinter> (\<top> \<^emph>\<and> q)\<close>
  \<open>(q \<^emph>\<and> \<S> p) = \<S> p \<sqinter> (q \<^emph>\<and> \<top>)\<close>
  by (force simp add: sepconj_conj_def fun_eq_iff)+


end