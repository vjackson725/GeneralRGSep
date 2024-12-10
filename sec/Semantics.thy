theory Semantics
  imports "../Soundness"
begin

datatype pair_sem_st = Running | CrashLeak | CrashPair

type_synonym 's ptrace = \<open>'s list \<times> pair_sem_st\<close>


text \<open>
  Note the the most recent state is at the *head* of the list.
  e.g. [sn, s{n-1}, ..., s1, s0]
\<close>
inductive pair_trsem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) pstate \<times> ('l \<times> 's, unit) pstate) ptrace \<Rightarrow>
      bool\<close>
  where
    init: \<open>pair_trsem r F ([xy], Running)\<close>
  | rely_step_left:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (((l1,s1),c1), sc2) \<Longrightarrow>
      r s1 s1' \<Longrightarrow>
      pair_trsem r F ((((l1,s1'),c1), sc2) # t, Running)\<close>
  | rely_step_right:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, ((l2,s2),c2)) \<Longrightarrow>
      r s2 s2' \<Longrightarrow>
      pair_trsem r F ((sc1, ((l2,s2'),c2)) # t, Running)\<close>
  | left_plain_step:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, sc2) \<Longrightarrow>
      sc1 \<midarrow>a\<rightarrow> (Inl s1', c1') \<Longrightarrow>
      pair_trsem r F (((s1', c1'), sc2) # t, Running)\<close>
  | right_plain_step:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, sc2) \<Longrightarrow>
      sc2 \<midarrow>a\<rightarrow> (Inl s2', c2') \<Longrightarrow>
      pair_trsem r F ((sc1, (s2', c2')) # t, Running)\<close>
  | left_framed_step:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (((hl1,hs1),c1), sc2) \<Longrightarrow>
      F (hlf1, hs1) \<Longrightarrow>
      hl1 ## hlf1 \<Longrightarrow>
      ((hl1 + hlf1, hs1), c1) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf1', hs1'), c1') \<Longrightarrow>
      (\<exists>hl1'.
          hl1' ## hlf1 \<and>
          hlhlf1' = hl1' + hlf1 \<and>
          (\<alpha> = Tau \<longrightarrow> hl1' = hl1) \<and>
          t' = (((hl1',hs1'),c1'), sc2) # t) \<Longrightarrow>
      pair_trsem r F (t', Running)\<close>
  | right_framed_step:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, ((hl2,hs2),c2)) \<Longrightarrow>
      F (hlf2, hs2) \<Longrightarrow>
      hl2 ## hlf2 \<Longrightarrow>
      ((hl2 + hlf2, hs2), c2) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf2', hs2'), c2') \<Longrightarrow>
      (\<exists>hl2'.
        hl2' ## hlf2 \<and>
        hlhlf2' = hl2' + hlf2 \<and>
        (\<alpha> = Tau \<longrightarrow> hl2' = hl2) \<and>
        t' = (sc1, ((hl2',hs2'),c2')) # t) \<Longrightarrow>
      pair_trsem r F (t', Running)\<close>
  | crash_leak:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, sc2) \<Longrightarrow>
      sc1 \<midarrow>|\<rightarrow>               \<and> sc2 \<midarrow>a\<rightarrow> (Inr (), c1') \<or>
      sc1 \<midarrow>a\<rightarrow> (Inr (), c2') \<and> sc2 \<midarrow>|\<rightarrow>                 \<Longrightarrow>
      pair_trsem r F (t, CrashLeak)\<close>
  | crash_paired:
    \<open>pair_trsem r F (t, Running) \<Longrightarrow>
      hd t = (sc1, sc2) \<Longrightarrow>
      sc1 \<midarrow>a\<rightarrow> (Inr (), c1') \<Longrightarrow>
      sc2 \<midarrow>a\<rightarrow> (Inr (), c2') \<Longrightarrow>
      pair_trsem r F (t, CrashPair)\<close>

end