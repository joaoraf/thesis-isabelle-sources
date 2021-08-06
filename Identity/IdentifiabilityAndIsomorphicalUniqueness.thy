text_raw \<open>\subsection[Identifiability, Isomorphical Uniqueness and Permutability]{Identifiability, Isomorphical Uniqueness and Permutability\isalabel{identifiability-iso-uniqueness}}\<close>

theory IdentifiabilityAndIsomorphicalUniqueness
  imports Identifiability
  "../ParticularStructures/StructuralPropertiesTheorems"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  While we introduced, in the previous section, a definition for
  what consists the ``identity'' of a particular in terms of the
  existence of a suitable \emph{identifying predicate}, in this
  section we show that it is not necessary to refer to the existence
  of an 
  element that is ontologically extraneous to the UFO particular
  structure (the identifying predicate), to characterize the concept
  of the ``identity'' of a particular. 

  We achive this by proving the logical equivalence between the
  notion of identifiability, as described in the previous section,
  and the notions of isomorphical uniqueness and non-permutability,
  that were introduced in \autoref{subsec:isomorphical-uniqueness} 
  and \autoref{subsec:permutability}.
\<close>

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> ex1_intro_1:
  fixes A and P
  assumes \<open>f \<in> A\<close> \<open>\<And>g. g \<in> A \<Longrightarrow> g a = f a\<close>  
  shows \<open>\<exists>!z. \<forall>g \<in> A. g a = z\<close>
  apply (intro ex1I[of _ \<open>f a\<close>] ballI)
  subgoal using assms by blast
  subgoal premises P for z
    using P[rule_format,OF assms(1)] 
    by simp
  done

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The equivalence of the set of isomorphically-unique particulars
  and the set of identifiable particulars is shown by the following
  lemmas and theorem:
\<close>

lemma  im_uniques_are_identifiables: \<open>\<P>\<^sub>\<simeq>\<^sub>! \<subseteq> \<P>\<^sub>=\<close>
proof (intro subsetI)
  fix x
  assume as: \<open>x \<in> \<P>\<^sub>\<simeq>\<^sub>!\<close>
  obtain \<open>x \<in> \<E>\<close> using as by blast

  have A: \<open>\<sigma> x = \<phi> x\<close> 
    if \<open>inj_on \<phi> \<E>\<close> 
       \<open>particular_struct_morphism \<Gamma> (MorphImg \<phi> \<Gamma>) \<sigma>\<close>
    for \<phi>  \<sigma> :: \<open>'p \<Rightarrow> ZF\<close>
    apply (rule as[THEN isomorphically_unique_particulars_E])
    subgoal premises P
      apply (rule P(2)[simplified,OF conjI
                ,OF that(1)[simplified] _ that(2) \<open>x \<in> \<E>\<close>,
                THEN iffD2])
      using inj_on_id by blast+
    done

  have pick_ex: \<open>\<exists>!y. \<forall>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>. \<phi>' x = y\<close> 
    if as1: \<open>\<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> for \<Gamma>'
  proof -
    obtain \<phi>\<^sub>1 where phi1:
        \<open>\<phi>\<^sub>1 \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> 
        \<open>\<Gamma>' = MorphImg \<phi>\<^sub>1 \<Gamma>\<close>    
      using as1 by blast  
    interpret phi1: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<^sub>1\<close> using phi1 by simp
    interpret phi1_inv: particular_struct_bijection_1 \<open>MorphImg \<phi>\<^sub>1 \<Gamma>\<close> \<open>phi1.inv_morph\<close>
      using particular_struct_bijection_iff_particular_struct_bijection_1 by blast

    have AA: \<open>\<phi>\<^sub>1 \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>
      apply (auto)      
      using phi1(2) phi1.particular_struct_morphism_axioms 
      by blast

    have BB: \<open>\<phi>' x = \<phi>\<^sub>1 x\<close> if as2: \<open>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close> for \<phi>'    
      apply (rule A)
      subgoal using phi1.morph_is_injective[simplified] .
      using phi1(2) as2 morphs_D by metis

    show \<open>?thesis\<close>
      apply (rule ex1_intro_1[of \<open>\<phi>\<^sub>1\<close>])
      subgoal using AA .
      subgoal premises P for \<phi>'
        using BB[OF P] .
      done
  qed
  
  show \<open>x \<in> \<P>\<^sub>=\<close>
  proof (clarsimp simp:  identifiables_def \<open>x \<in> \<E>\<close>)    
    
    define P where \<open>P \<Gamma>' z \<longleftrightarrow> z = (THE y. \<forall>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>. \<phi>' x = y)\<close> for \<Gamma>' and z :: \<open>ZF\<close>

    have P1: \<open>P \<Gamma>' (\<phi>' x)\<close> 
      if \<open>\<exists>\<phi>\<in>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>. \<Gamma>' = MorphImg \<phi> \<Gamma>\<close> \<open>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close> for \<Gamma>' \<phi>'
      using pick_ex[THEN the1I2,of \<open>\<Gamma>'\<close> \<open>\<lambda>y. \<forall>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>. \<phi>' x = y\<close>,
        simplified P_def[symmetric],simplified] that by metis
    have P2: \<open>P (MorphImg \<phi> \<Gamma>) (\<phi>' x)\<close>
      if \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> \<open>\<phi>' \<in> Morphs\<^bsub>\<Gamma>, MorphImg \<phi> \<Gamma>\<^esub>\<close> for \<phi> \<phi>'
      using P1 that by metis    
    
    have P3: \<open>y = \<phi> x\<close>
      if as3: \<open>\<sigma> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<sigma> \<Gamma>\<^esub>\<close> 
              \<open>P (MorphImg \<sigma> \<Gamma>) y\<close>  for \<sigma> \<phi> y
      apply (rule the1_equality[of \<open>\<lambda>y. \<forall>\<phi>' \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<sigma> \<Gamma>\<^esub>. \<phi>' x = y\<close>,of \<open>\<phi> x\<close>,
              simplified as3(3)[simplified P_def,symmetric],OF pick_ex]
              ; (intro ballI)?) 
      subgoal G1 using that(1) by blast
      subgoal for \<phi>\<^sub>3
        apply auto        
        by (metis G1 morphs_iff pick_ex that(2))
      done
         
    show \<open>\<exists>P. identity_pred \<Gamma> P x\<close> 
      apply (intro exI[of _ \<open>P\<close>] identity_pred_I1 iffI )
      subgoal by (simp add: \<open>x \<in> \<E>\<close>)
      subgoal by (metis (full_types) P3 as isomorphic_models_E ufo_particular_theory_sig.isomorphically_unique_particulars_E)                
      using P2 \<open>x \<in> \<E>\<close> by auto
  qed
qed

lemma identifiables_are_im_uniques: \<open>\<P>\<^sub>= \<subseteq> \<P>\<^sub>\<simeq>\<^sub>!\<close>
proof (intro subsetI)
  fix x
  assume \<open>x \<in> \<P>\<^sub>=\<close>
  then obtain P where P: \<open>x \<in> \<E>\<close> \<open>identity_pred \<Gamma> P x\<close> by blast  
  show \<open>x \<in> \<P>\<^sub>\<simeq>\<^sub>!\<close>
  proof (rule)
    show \<open>x \<in> \<E>\<close> using P(1) .
    fix \<phi> \<sigma> y
    assume as: \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> \<open>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close>
    have P1: \<open>identity_pred (MorphImg \<phi> \<Gamma>) P (\<phi> x)\<close>
      using identity_respects_isomorphisms[OF P(2) as(1)] .
    interpret phi: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
      using as(1) by blast
    have A: \<open>phi.tgt.\<Gamma> = MorphImg \<phi> \<Gamma>\<close> 
      using phi.tgt_Gamma_eq_Morph_img by auto
    have B: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close>
      using as(1) by (meson bijections1_are_morphisms)
    note C = identity_pred_eqI[
               where \<phi> = \<open>\<phi>\<close> and x = \<open>x\<close> and P = \<open>P\<close> and \<sigma> = \<open>\<phi>\<close>,
                 OF P(2) as(1) B]
             identity_pred_eqI[
               where \<phi> = \<open>\<sigma>\<close> and x = \<open>x\<close> and P = \<open>P\<close> and \<sigma> = \<open>\<phi>\<close>,
                 OF P(2) as(1,2)]        
    have D: \<open>P (MorphImg \<phi> \<Gamma>) (\<sigma> x) \<longleftrightarrow> P (MorphImg \<phi> \<Gamma>) (\<phi> x)\<close>      
      by (metis C(1) C(2) P(1))
    have E: \<open>\<phi> x = \<sigma> x \<longleftrightarrow> P (MorphImg \<phi> \<Gamma>) (\<phi> x)\<close>
      using C(2)[of \<open>\<phi> x\<close>]      
      using P(1) P(2) identity_pred phi.morph_is_injective by auto
    have E1: \<open>MorphImg \<phi> \<Gamma> \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> 
      using as(1) by blast
    obtain F: \<open>\<And>\<Gamma>' \<phi> y. \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> P \<Gamma>' y = (\<forall>z\<in>phi.src.endurants. (y = \<phi> z) = (z = x))\<close>
      using P(2)[THEN identity_pred_E] by metis
    note G = F[OF E1 as(2)]
    note H = C(1)[simplified C(2)]
    note J = H[THEN iffD1,simplified Ball_def,simplified,rule_format]
             H[THEN iffD2,simplified Ball_def,simplified,rule_format]
    show \<open>\<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>
      apply (intro iffI)
      subgoal using G P(2) as(3) identity_pred phi.particular_struct_bijection_1_axioms by auto
      subgoal using J by (metis E P(2) identity_pred phi.morph_is_injective ufo_particular_theory_sig.\<Gamma>_simps(2))
      done      
  qed
qed

theorem identifiables_are_the_im_uniques: \<open>\<P>\<^sub>= = \<P>\<^sub>\<simeq>\<^sub>!\<close>
  using im_uniques_are_identifiables
      identifiables_are_im_uniques
  by blast

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Since the set of isomorphically unique particulars is
  equivalent to the set of non-permutable particulars,
  then we can also say that the identifiable particulars
  are exactly those that are non-permutable:\<close>
     
theorem identifiables_are_the_non_permutables: \<open>\<P>\<^sub>= = \<P>\<^sub>1\<^sub>!\<close>
  using identifiables_are_the_im_uniques
  by (simp add: non_permutable_particulars_are_the_unique_particulars)    


end

end
