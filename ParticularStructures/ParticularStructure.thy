text_raw \<open>\section[Particular Structures]{Particular Structures\isalabel{sec:particular-structures}}\<close>

theory ParticularStructure
  imports "../Particulars/Particulars"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this chapter, we present a category of UFO particular structures, whose
  objects are Isabelle/HOL records that encode a model of the UFO theory of
  particulars presented in \autoref{cha:simplified-ufo-theory}.
  
  The record that encodes a particular structure is defined as follows:
\<close>

record ('p,'q) particular_struct =
  ps_quality_spaces :: \<open>'q set set\<close>
  ps_worlds :: \<open>'p set set\<close> 
  ps_inheres_in :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close>  
  ps_assoc_quale :: \<open>'p \<Rightarrow> 'q \<Rightarrow> bool\<close>  
  ps_towards :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> 

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The six fields of the particular structure record represent the formal elements of the
  UFO particular theory:
  \begin{itemize}
  \item \texttt{ps\_worlds}: The set of possible worlds (\<open>\<W>\<close>)
  \item \texttt{ps\_inheres\_in}: The inherence relationship (\<open>\<triangleleft>\<close>)
  \item \texttt{ps\_quality\_spaces}: The set of quality spaces (\<open>\<Q>\<S>\<close>)
  \item \texttt{ps\_assoc\_quale}: The relationship of quale association (\<open>\<leadsto>\<close>)
  \item \texttt{ps\_towards}: The towardness relation (\<open>\<longlongrightarrow>\<close>)
  \end{itemize}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_eqI[intro!]:
  fixes M\<^sub>1 M\<^sub>2 :: \<open>('p,'q) particular_struct\<close>
  assumes
    \<open>ps_quality_spaces M\<^sub>1 = ps_quality_spaces M\<^sub>2\<close>
    \<open>ps_worlds M\<^sub>1 = ps_worlds M\<^sub>2\<close>
    \<open>ps_inheres_in M\<^sub>1 = ps_inheres_in M\<^sub>2\<close>
    \<open>ps_assoc_quale M\<^sub>1 = ps_assoc_quale M\<^sub>2\<close>
    \<open>ps_towards M\<^sub>1 = ps_towards M\<^sub>2\<close>
  shows \<open>M\<^sub>1 = M\<^sub>2\<close>
  using assms by auto

locale particular_struct_sig =
  fixes
    \<Gamma> :: \<open>('p,'q) particular_struct\<close> and
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 

context particular_struct_sig
begin

abbreviation \<^marker>\<open>tag aponly\<close> \<open>\<W> \<equiv> ps_worlds \<Gamma>\<close>

abbreviation \<^marker>\<open>tag aponly\<close> inheresIn (infix \<open>\<triangleleft>\<close> 75) where
  \<open>inheresIn \<equiv> ps_inheres_in \<Gamma>\<close>

abbreviation \<^marker>\<open>tag aponly\<close> assoc_quale (infix \<open>\<leadsto>\<close> 75) where
  \<open>assoc_quale \<equiv> ps_assoc_quale \<Gamma>\<close>

abbreviation \<^marker>\<open>tag aponly\<close> towards (infix \<open>\<longlongrightarrow>\<close> 75) where
  \<open>(\<longlongrightarrow>) \<equiv> ps_towards \<Gamma>\<close>

abbreviation \<^marker>\<open>tag aponly\<close> \<open>\<Q>\<S> \<equiv> ps_quality_spaces \<Gamma>\<close>

end

definition \<^marker>\<open>tag aponly\<close> (in ufo_particular_theory_sig) \<Gamma> 
  :: \<open>('p,'q) particular_struct\<close> where
  \<open>\<Gamma> \<equiv> \<lparr>
      ps_quality_spaces = \<Q>\<S>,
      ps_worlds = \<W>,
      ps_inheres_in = inheresIn,
      ps_assoc_quale = assoc_quale,
      ps_towards = towards
   \<rparr>\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> (in ufo_particular_theory_sig) 
    \<Gamma>_simps[simp]:
  \<open>ps_quality_spaces \<Gamma> = \<Q>\<S>\<close>
  \<open>ps_worlds \<Gamma> = \<W>\<close>
  \<open>ps_inheres_in \<Gamma> = inheresIn\<close>
  \<open>ps_assoc_quale \<Gamma> = assoc_quale\<close>
  \<open>ps_towards \<Gamma> = towards\<close>
  using \<Gamma>_def by auto


locale particular_struct_defs =
    particular_struct_sig 
      where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    ufo_particular_theory_sig where 
      \<Q>\<S> = \<open>\<Q>\<S>\<close> and
      \<W> = \<open>\<W>\<close> and
      inheresIn = \<open>inheresIn\<close> and
      assoc_quale = \<open>assoc_quale\<close> and
      towards = \<open>towards\<close> and
      Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for 
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>  

locale particular_struct =
    particular_struct_defs where 
      Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  +
    ufo_particular_theory where 
      \<Q>\<S> = \<open>\<Q>\<S>\<close> and
      \<W> = \<open>\<W>\<close> and
      inheresIn = \<open>inheresIn\<close> and
      assoc_quale = \<open>assoc_quale\<close> and
      towards = \<open>towards\<close> and
      Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for 
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> ufo_theory_and_particular_struct_eq[simp]:
  fixes 
    \<W> \<Q>\<S> assoc_quale 
    universal_qualia_set inheresIn 
    charSet towards
  shows    
    \<open>particular_struct (
        ufo_particular_theory_sig.\<Gamma> 
          \<W> inheresIn \<Q>\<S> assoc_quale towards) \<longleftrightarrow>
     ufo_particular_theory 
          \<W> inheresIn \<Q>\<S> assoc_quale towards
     \<close>
    (is \<open>?B \<longleftrightarrow> ?A\<close>)
proof -
  note S = ufo_particular_theory_sig.\<Gamma>_simps
  show \<open>?thesis\<close>
  proof
    assume \<open>?A\<close>
    then interpret 
        ufo_particular_theory \<open>\<W>\<close> \<open>inheresIn\<close> 
           \<open>\<Q>\<S>\<close> \<open>assoc_quale\<close> \<open>towards\<close> by simp
    show \<open>?B\<close>
      apply (intro_locales ; simp only: S)
      subgoal 
        by (simp add: possible_worlds_axioms)
      subgoal 
        by (simp add: inherence_base.axioms(2) 
                  inherence_base_axioms)
      subgoal 
        by (simp add: noetherian_inherence_axioms_def)
      subgoal 
        by (simp add: inherence_axioms_def)
      subgoal 
        by (simp add: quality_space_axioms)
      subgoal 
        by (simp add: qualified_particulars.axioms(3) 
                qualified_particulars_axioms)
      subgoal
        using towardness_axioms towardness_def 
        by blast
      using just_ufo_particular_theory_axioms 
            ufo_particular_theory_axioms_def 
      by blast
  next
    assume \<open>?B\<close>
    then interpret particular_struct 
      \<open>ufo_particular_theory_sig.\<Gamma> 
        \<W> inheresIn \<Q>\<S> assoc_quale towards\<close>
      by simp
    show \<open>?A\<close>
      using ufo_particular_theory_axioms 
      by (simp only: S)
  qed
qed

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_valid[intro!,simp]: \<open>particular_struct \<Gamma>\<close> 
  using ufo_theory_and_particular_struct_eq 
        ufo_particular_theory_axioms 
  by simp

end

abbreviation \<^marker>\<open>tag aponly\<close> \<open>particulars \<Gamma> \<equiv> 
  possible_worlds_sig.\<P> (ps_worlds \<Gamma>)\<close>

end