section \<open>Finite Particular Structures\<close>

theory FiniteParticularStructure
  imports
    "../ParticularStructures/InverseImageMorphismChoice"
    "../Identity/Individuality"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We present a theory of sortality in a context that imposes some
  restrictions on the UFO particular theory. Namely, we require
  that the set of particulars of the UFO particular structures
  be \emph{finite} and that all the particulars possess 
  \emph{individuality} already, i.e. are non-collapsible.  
\<close>
text_raw  \<open>\par\<close>
locale finite_particulars_with_individuality = 
    ufo_particular_theory where Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>p = Typ\<^sub>p
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> +
  assumes 
    finite_particulars[intro!,simp]: \<open>finite \<P>\<close> and
    particulars_have_individuality: \<open>\<P> = \<P>\<^sub>i\<^sub>n\<^sub>d\<close>
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Under this restriction, any injective morphism
  to an isomorphic structure is also a bijection:
\<close>
text_raw  \<open>\par\<close>

lemma mono_to_iso_is_an_iso:
  assumes 
    \<open>particular_struct_injection \<Gamma> \<Gamma>' \<phi>\<close>
    \<open>\<exists>\<sigma>. particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>\<close>
  shows \<open>particular_struct_bijection \<Gamma> \<Gamma>' \<phi>\<close>
proof -
  interpret phi: particular_struct_injection \<Gamma> \<Gamma>' \<phi>
    using assms by simp
  obtain \<sigma> where \<open>particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>\<close>
    using assms by blast
  then interpret sigma: particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>
    by simp
  have A: \<open>finite (particulars \<Gamma>')\<close>
    using finite_particulars sigma.morph_bijective 
      sigma.morph_image_def 
    by auto
  have \<open>bij_betw \<phi> \<P> phi.tgt.\<P>\<close>
    using sigma.morph_bijective phi.morph_is_injective
    A finite_particulars 
    by (metis \<Gamma>_simps(2) bij_betw_def card_image card_mono card_seteq
        phi.morph_image_def phi.morph_scope)
  then show ?thesis
    apply (unfold_locales)    
    by (simp add: bij_betw_def)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
   Furthermore, any morphism to an isomorphic structure is
   an injection (and thus a bijection).
\<close>
text_raw  \<open>\par\<close>
lemma morphism_to_injective:
  assumes 
    \<open>particular_struct_morphism \<Gamma> \<Gamma>' \<phi>\<close>
    \<open>\<exists>\<sigma>. particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>\<close>
  shows \<open>particular_struct_injection \<Gamma> \<Gamma>' \<phi>\<close>
proof -
  interpret phi: particular_struct_morphism \<Gamma> \<Gamma>' \<phi>
    using assms by simp
  obtain \<sigma> where \<open>particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>\<close>
    using assms by blast
  then interpret sigma: particular_struct_bijection \<Gamma> \<Gamma>' \<sigma>
    by simp
  interpret inv_sigma_phi:
    particular_struct_endomorphism \<Gamma> \<open>sigma.inv_morph \<circ> \<phi>\<close>
    apply (simp only: particular_struct_endomorphism_def
        ; intro conjI)
    subgoal by unfold_locales
    subgoal
      apply (intro particular_struct_morphism_comp[of _ \<Gamma>'] conjI)
      subgoal by unfold_locales
      using particular_struct_bijection_def particular_struct_injection_def by blast
    done
  have inv_sigma_phi: \<open>sigma.inv_morph \<circ> \<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
    using inv_sigma_phi.particular_struct_endomorphism_axioms 
    by blast
  have P1: \<open>finite (particulars \<Gamma>')\<close>
    using finite_particulars sigma.morph_bijective[simplified] 
    using bij_betw_finite by blast
  then have P2: \<open>card (particulars \<Gamma>') = card \<P>\<close>
    using finite_particulars sigma.morph_bijective[simplified]
    using bij_betw_same_card by fastforce
  have \<open>inj_on \<phi> \<P>\<close>
  proof (rule ccontr)
    assume \<open>\<not> inj_on \<phi> \<P>\<close>  
    then obtain x y where 
        AA: \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> \<open>x \<noteq> y\<close> \<open>\<phi> x = \<phi> y\<close>        
      by (meson inj_onI)
    obtain \<upsilon> where BB: \<open>particular_struct_endomorphism \<Gamma> \<upsilon>\<close>
        \<open>\<upsilon> x = y\<close> \<open>\<upsilon> y = y\<close>
      using phi.choice[simplified,OF AA(1,2,4)] by metis
    then have CC: \<open>\<upsilon> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> by blast
    obtain A: \<open>x \<in> \<P>\<^sub>i\<^sub>n\<^sub>d\<close> \<open>y \<in> \<P>\<^sub>i\<^sub>n\<^sub>d\<close>
      using particulars_have_individuality AA by metis
    then obtain B: \<open>\<not> collapsible x\<close> \<open>\<not> collapsible y\<close>
      using particularsWithIndividualityE by blast
    show False
      using B(1)[simplified,rule_format,
        of \<upsilon>,OF AA(1) CC AA(2)] AA(3) BB(2,3) by metis
  qed
  then show ?thesis
    by (unfold_locales  ; simp)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Consequently, all endomorphisms are bijective and, thus
  are permutation morphisms:
\<close>
text_raw  \<open>\par\<close>

lemma  all_endomorphisms_are_perms: \<open>EndoMorphs\<^bsub>\<Gamma>\<^esub> \<subseteq> Perms\<^bsub>\<Gamma>\<^esub>\<close>
proof (intro subsetI permutations_I ; drule endomorphisms_D)
  fix \<phi>
  assume A: \<open>particular_struct_endomorphism \<Gamma> \<phi>\<close>
  then interpret phi: particular_struct_endomorphism  \<Gamma> \<phi> .
  have B: \<open>\<exists>\<sigma>. particular_struct_bijection \<Gamma> \<Gamma> \<sigma>\<close>
    apply (intro exI[of _ id])    
    using particular_struct_permutation_def by blast  
  then have C: \<open>particular_struct_injection \<Gamma> \<Gamma> \<phi>\<close>
    using morphism_to_injective phi.particular_struct_morphism_axioms 
    by metis
  then have D: \<open>particular_struct_bijection \<Gamma> \<Gamma> \<phi>\<close>
    using mono_to_iso_is_an_iso B by metis
  then interpret phi_iso: particular_struct_bijection \<Gamma> \<Gamma> \<phi> .
  show \<open>particular_struct_permutation \<Gamma> \<phi>\<close>
    by (intro_locales)
qed

end


end
