theory Security
  imports "../Security"
begin

lemma basic_tau_aact_exclusive:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha> \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>'\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha>'\<close>
  apply (frule aopstep_tau_preserves_state, force)
  apply (induct \<pi>\<alpha> sc sc' arbitrary: \<pi>\<alpha>' rule: aopstep.induct)
        apply force
       apply force
      apply force
    (* endet *)
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (rename_tac s' c' \<alpha>')
     apply (case_tac \<open>ca = Skip \<and> cb = Skip\<close>)
      apply force
     apply (clarsimp simp add: vis_tau_aact_incompatible(2))
  subgoal sorry
      (* par *)
    apply clarsimp
  subgoal sorry
      (* do-loop *)
  subgoal sorry
      (* atom *)
  apply force
  oops

lemma basic_tau_reducts_from_basic_tau_exec:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all (basic_tau_aact \<circ> snd) \<rho>' \<Longrightarrow>
    length \<rho> \<le> length \<rho>' \<Longrightarrow>
    fst sc' = fst sc \<and> list_all (basic_tau_aact \<circ> snd) \<rho>\<close>
  apply (induct arbitrary: \<rho>' rule: aopsteps.induct)
   apply clarsimp
  oops


subsection \<open> aaa \<close>

definition
  \<open>sec_core p \<equiv>
    (\<lambda>(x,y). (p \<circ> exch4) (x,y) \<and> (p \<circ> exch4) (y, x) \<and> (p \<circ> exch4) (x, x) \<and> (p \<circ> exch4) (y, y)) \<circ> exch4\<close>

definition
  \<open>sec_ext p \<equiv>
    (\<lambda>(x,y). (p \<circ> exch4) (x,y) \<or> (p \<circ> exch4) (y, x) \<or>
      (x = y \<and> (\<exists>z. (p \<circ> exch4) (x, z) \<and> (p \<circ> exch4) (z, y)))
    ) \<circ> exch4\<close>

lemma
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  shows
  \<open>sec_core p \<le> quasireflp_steprel r \<Longrightarrow>
    sec_core p \<le> symp_steprel r \<Longrightarrow>
    sp r (sec_core p) \<le> sec_core (sp r p)\<close>
  apply (clarsimp simp add: sec_core_def exch4_def le_fun_def quasireflp_steprel_def
      symp_steprel_def sp_def)
  apply metis
  done

lemma
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  shows
  \<open>sec_core p \<le> quasireflp_steprel r \<Longrightarrow>
    sec_core p \<le> symp_steprel r \<Longrightarrow>
    q = sp r (sec_core p) \<Longrightarrow>
    q' = sec_core (sp r p) \<Longrightarrow>
    q' \<le> q\<close>
(*  nitpick[card 'l=2, card 's=1] *)
  oops
(*
    p = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    q = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    q' = (\<lambda>x. _)
         (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
            ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True)
    r = (\<lambda>x. _)
        (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) :=
           (\<lambda>x. _)
           (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
              ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True),
           ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True),
           ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := True,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False),
           ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) :=
             (\<lambda>x. _)
             (((l\<^sub>1, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>1, l\<^sub>2), s\<^sub>1, s\<^sub>1) := False, ((l\<^sub>2, l\<^sub>1), s\<^sub>1, s\<^sub>1) := False,
                ((l\<^sub>2, l\<^sub>2), s\<^sub>1, s\<^sub>1) := True))
*)


section \<open> Scratch Space \<close>

definition
  \<open>symp_atoms \<equiv> all_atom_comm
    (\<lambda>ar. \<forall>lx sx ly sy lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx')))\<close>

lemma symp_atomsD:
  \<open>symp_atoms cc \<Longrightarrow> ar \<in># all_atoms cc \<Longrightarrow>
    ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<Longrightarrow>
    ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx'))\<close>
  by (simp add: all_atom_comm_def symp_atoms_def, blast)

lemmas symp_atoms_simps[simp] =
  all_atom_comm_simps[of \<open>\<lambda>ar. \<forall>lx sx ly sy lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx'))\<close>,
    simplified symp_atoms_def[symmetric]]

text \<open> Old definition of security from Jul-Aug that doesn't quite work \<close>
inductive secure_old
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<times> ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      ('l, 's) secstate \<Rightarrow>
      bool\<close>
  for R F G I q
  where secure_oldI[intro]:
  \<open>zz = ((slx::'l, ssx::'s), (sly::'l, ssy::'s)) \<Longrightarrow>
    \<comment> \<open> Post-condition
         Note that \<^emph>\<open>both\<close> programs need to be terminated. \<close>
    cx = Skip \<longrightarrow> cy = Skip \<longrightarrow> q ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> State Invariant \<close>
    I ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> Rely Steps \<close>
    (\<And>n' ssx' ssy'.
      n = Suc n' \<Longrightarrow>
      R (ssx, ssy) (ssx', ssy') \<Longrightarrow>
      secure_old R F G I q n' (cx, cy) ((slx, ssx'), (sly, ssy'))) \<Longrightarrow>
    \<comment> \<open> Opsteps \<close>
    (\<And>n' \<pi>\<alpha> sx' sy' cx' cy'.
      n = Suc n' \<Longrightarrow>
      ((slx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
      ((sly, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (snd sx', snd sy')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> fst sx' = slx \<and> fst sy' = sly) \<and>
      secure_old R F G I q n' (cx', cy') (sx', sy') ) \<Longrightarrow>
    \<comment> \<open> Framed opsteps \<close>
    (\<And>n' fx fy \<pi>\<alpha> slfx' slfy' ssx' ssy' cx' cy'.
      n = Suc n' \<Longrightarrow>
      F ((fx, fy), (ssx, ssy)) \<Longrightarrow>
      slx ## fx \<Longrightarrow>
      sly ## fy \<Longrightarrow>
      ((slx + fx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfx', ssx'), cx') \<Longrightarrow>
      ((sly + fy, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfy', ssy'), cy') \<Longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (ssx', ssy')) \<and>
      (\<exists>slx'.
        slx' ## fx \<and>
        slfx' = slx' + fx \<and>
        (\<exists>sly'.
          sly' ## fy \<and>
          slfy' = sly' + fy \<and>
          (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> slx' = slx \<and> sly' = sly) \<and>
          secure_old R F G I q n' (cx', cy') ((slx', ssx'), (sly', ssy')) ))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    secure_old R F G I q n (cx, cy) zz\<close>


subsection \<open> (Old) Safety Implies Security \<close>

theorem safety_implies_security_old:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and ss :: \<open>('l, 's) rgstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe R F G I q n cc ss\<close>
    \<open>cc = liftC c\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> all_sec_determ c \<circ> exch4\<close>
  shows
    \<open>secure_old R F G I q n (c, c) (exch4 ss)\<close>
  using assms
proof (induct arbitrary: c rule: safe.induct)
  case (safeI c' s n)
  obtain lsx lsy ssx ssy where
    \<open>s = ((lsx, lsy), (ssx, ssy))\<close>
    by (metis surjective_pairing)
  then show ?case
    using safeI.prems safeI.hyps(1-2)
    apply (clarsimp simp del: sup_apply comp_apply)
    apply (rule secure_oldI)
      (* subgoals: destructuring *)
         apply (simp add: exch4_def; fail)
      (* term *)
        apply (simp add: exch4_def; fail)
      (* subgoal: invariant *)
       apply force
      (* subgoal: rely *)
      apply (frule safeI.hyps(4), force, force, force)
      apply (simp add: exch4_def; fail)
      (* subgoal: double-step *)
     apply clarsimp
     apply (frule(1) same_initcomm_and_aact_then_same_fincomm[
          where sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close>])
      apply (simp add: le_fun_def exch4_def)
      apply (metis all_sec_determ_implies_head_sec_determ)
     apply (frule full_sync_double_aopstep_to_aopstep[
          where sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close>], blast)
      apply (simp add: le_fun_def exch4_def)
      apply (metis all_sec_determ_implies_head_sec_determ)
     apply (simp del: comp_apply add: exch4_two_apply)
     apply (frule safeI(5)[OF _ aopstep_then_opstep], blast)
     apply (frule aopstep_preserves_all_sec_determ)
     apply (intro conjI)
       apply force
      apply force
     apply (clarsimp simp del: sup_apply comp_apply del: disjCI)
     apply (meson leq_exch4_shunt order_trans)
        (* subgoal: framed double-step *)
    apply (subgoal_tac \<open>(I \<^emph>\<and> F) ((lsx + fx, lsy + fy), (ssx, ssy))\<close>)
     prefer 2
     apply (rule sepconj_conjI, assumption, assumption, force, force)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        same_initcomm_and_aact_then_same_fincomm, assumption)
     apply (simp add: le_fun_def exch4_def)
     apply (metis all_sec_determ_implies_head_sec_determ)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        full_sync_double_aopstep_to_aopstep)
      apply force
     apply (simp add: le_fun_def exch4_def)
     apply (metis all_sec_determ_implies_head_sec_determ)
    apply (clarsimp simp del: comp_apply)
    apply (frule_tac fs=\<open>(fx, fy)\<close> in safeI(6)[OF _ aopstep_then_opstep])
       apply force
      apply force
     apply force
    apply (frule aopstep_preserves_all_sec_determ)
    apply (clarsimp simp del: sup_apply comp_apply)
    apply (intro exI conjI, fast, fast, fast, fast, fast)
    apply (meson order.trans leq_exch4_shunt; fail)
    done
qed


end
