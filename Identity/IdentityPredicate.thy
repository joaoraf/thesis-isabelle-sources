text_raw \<open>\section[Identity Through Permutability]{Identity Through Permutability\isalabel{sec:identifiability}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section, we describe the formal characterization of the
  identity of particulars in UFO through the notion of permutability
  introduced in \autoref{cha:particular-structures}. We also present
  a characterization based on the existence of an identifying predicate
  and prove its logical equivalence to the definition based on 
  permutability.
\<close>
text_raw \<open>\par\<close>
text_raw \<open>\subsection[Isomorphically-Invariant Identity Predicates]{Isomorphically-Invariant Identity Predicates\isalabel{subsec:isomorphically-invariant}}\<close>


theory IdentityPredicate
  imports
    "../ParticularStructures/ParticularStructureMorphisms"
    "HOL-ZF.MainZF"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Before we present the characterization of identity through the structural
  notion of permutability, we first characterize the usual notion of 
  the identifiability of a particular, as the existence of a predicate,
  here called an identity predicate, that satisfies some requirements.

  Given a particular structure \<open>\<Gamma>\<close> and a particular \<open>x\<close> of \<open>\<Gamma>\<close>, we say
  that a binary predicate \<open>P\<close> over the set of particular structures and
  the set of particulars is an identity predicate for \<open>x\<close> of \<open>\<Gamma>\<close>
  if it satisfies the following conditions: 

  \begin{enumerate}
  \item it identifies \<open>x\<close> in \<open>\<Gamma>\<close>, i.e., it is only satisfied by \<open>x\<close> in \<open>\<Gamma>\<close>;
  \item even if we change the representation of particulars in \<open>\<Gamma>\<close>, i.e.
        by an isomorphism to another structure \<open>\<Gamma>'\<close>, the particular that
        corresponds to \<open>x\<close> in \<open>\<Gamma>'\<close> is still identifiable by \<open>P\<close>.
  \end{enumerate}

  The reason we require invariance under isomorphisms (or change of representation) is that the predicate should rely only on the structure
  of \<open>\<Gamma>\<close> and not in the particularities of whatever representation is being
  used for particulars in \<open>\<Gamma>\<close>. For example, suppose we represent particulars
  as integers and suppose \<open>x\<close> is represented as the integer \<open>12\<close>. A predicate
  defined as \<open>P \<Gamma> y \<equiv> y = 12\<close> would surely identify \<open>x\<close> in \<open>\<Gamma>\<close>. Furthermore,
  it identifies \<open>x\<close> without using any properties or relations provided by the
  UFO theory of particulars (inherence, quale association, towardness). However,
  this predicate would fail in case we change the representation by using, for example, the morphism \<open>\<phi> x = x + 1\<close>.

  However, if the predicate ``fixes'' \<open>x\<close>'s identity by using only the 
  properties and relations provided by the UFO theory of particulars, which
  compose the UFO particular structure, then it is invariant under isomorphisms. 
  For example, suppose the same \<open>x\<close> in the previous example bears a moment \<open>m\<close>
  associated with a certain quale \<open>q\<close>. Suppose also that \<open>x\<close> is the only 
  particular in \<open>\<Gamma>\<close> that bears a moment associated to \<open>q\<close>. In that case, the
  predicate \<open>P \<Gamma> y \<equiv> \<exists>z. z \<triangleleft>\<^bsub>\<Gamma>\<^esub> y \<and> z \<longlongrightarrow> q\<close> is an (isomorphically invariant)
  identifying predicate for \<open>x\<close> of \<open>\<Gamma>\<close>.

  To express this definition in Isabelle/HOL we face a challenge due to
  the limited polymorphism provided by the Isabelle/HOL type system, which
  does not allow us to quantify over types (and thus, over representations
  for particulars). Instead, we require the predicate to be invariant 
  under isomorphisms from \<open>\<Gamma>\<close> to particular structures built with 
  Zermelo-Fraenkel sets as particular representations. We do so assuming
  that the Isabelle/HOL type of ZF sets is sufficiently large to include
  an infinite number of sets that are isomorphic to the set of particulars
  of \<open>\<Gamma>\<close>.

  Formally, we have an identity predicate defined as:  
\<close>
text_raw \<open>\par\<close>
definition identity_pred :: 
  \<open>('p,'q) particular_struct \<Rightarrow> 
   ((ZF,'q) particular_struct \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> bool\<close>  
  where \<open>
    identity_pred \<Gamma> P x \<longleftrightarrow> x \<in> particulars \<Gamma> \<and>
      BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset> \<and>
      (\<forall>\<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>.
        \<forall>\<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>. 
        \<forall>y. P \<Gamma>' y \<longleftrightarrow> 
          (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x))\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_I:
  assumes 
    \<open>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close>
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
    \<open>x \<in> particulars \<Gamma>\<close>
  shows \<open>identity_pred \<Gamma> P x\<close>
  using assms 
  by (auto simp: identity_pred_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_I':
  assumes 
    \<open>x \<in> particulars \<Gamma>\<close>
    \<open>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close>
        \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
  shows \<open>identity_pred \<Gamma> P x\<close>
  using assms 
  by (auto simp: identity_pred_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_E:
  assumes 
    \<open>identity_pred \<Gamma> P x\<close>
  obtains \<phi> where
    \<open>particular_struct \<Gamma>\<close>
    \<open>x \<in> particulars \<Gamma>\<close>
    \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>    
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close>    
proof -
  obtain \<phi> where A: 
    \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    using assms
    by (auto simp: identity_pred_def)
  have B: \<open>particular_struct \<Gamma>\<close> using A(1)  
    by (meson bijections1_are_morphisms morphs_D
              particular_struct_morphism.axioms(1)
              pre_particular_struct_morphism_def)    
  show \<open>?thesis\<close>
    using B assms that
    by (auto simp: identity_pred_def)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_E':
  assumes \<open>identity_pred \<Gamma> P x\<close>
  obtains
    \<open>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close>
    \<open>x \<in> particulars \<Gamma>\<close>
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close> 
  using assms   
  by (simp add: identity_pred_def) 
  

lemma \<^marker>\<open>tag (proof) aponly\<close> id_is_unique_1:  
  fixes \<Gamma> :: \<open>('p,'q) particular_struct\<close> and \<sigma> :: \<open>'p \<Rightarrow> ZF\<close>
  assumes 
    \<open>identity_pred \<Gamma> P\<^sub>1 x\<close> 
    \<open>identity_pred \<Gamma> P\<^sub>2 x\<close>
    \<open>particular_struct_bijection \<Gamma> \<Gamma>' \<phi>\<close>
    and \<sigma>: \<open>inj \<sigma>\<close>
  shows \<open>P\<^sub>1 (MorphImg \<sigma> \<Gamma>') y = P\<^sub>2 (MorphImg \<sigma> \<Gamma>') y\<close>
proof -    
  have sigma[dest!,simp]: \<open>\<sigma> x = \<sigma> y \<Longrightarrow> x = y\<close> for x y 
    using injD \<sigma> by metis
  have Gamma1[simp]: \<open>\<Gamma>' = MorphImg \<phi> \<Gamma>\<close> 
    using assms(3)
    by (meson isomorphism_iff_isomorphism_to_morphimg)
  interpret I1: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
    using assms(3) 
    by (simp add: 
          particular_struct_bijection_iff_particular_struct_bijection_1)
  have I1_src_gamma[simp]: \<open>I1.src.\<Gamma> = \<Gamma>\<close>  by simp  
  interpret IS2:  particular_struct \<open>MorphImg (\<sigma> \<circ> \<phi>) I1.src.\<Gamma>\<close>
    apply (intro I1.src.inj_morph_img_valid_structure)
    subgoal G1
      apply (intro comp_inj_on)
      subgoal G1_1 by simp
      subgoal G2_2
        apply (auto simp: possible_worlds_sig.\<P>_def)
        by (intro inj_onI ; simp)
      done
    subgoal G2 
      by (rule exI[of _ \<open>id\<close>] ; simp)
    done
  have simp1[simp]: \<open>particular_struct (MorphImg \<sigma> (MorphImg \<phi> \<Gamma>))\<close>
    using IS2.particular_struct_axioms 
    by (simp add: fcomp_def)
  have simp_worlds_img_img: 
      \<open>(\<sigma> ` \<phi> ` w\<^sub>1 = \<sigma> ` \<phi> ` w\<^sub>2) \<longleftrightarrow> (w\<^sub>1 = w\<^sub>2)\<close> 
      if \<open>w\<^sub>1 \<in> I1.src.\<W>\<close> \<open>w\<^sub>2 \<in> I1.src.\<W>\<close> for w\<^sub>1 w\<^sub>2        
    by (metis I1.phi_inv_phi_world \<sigma> inj_image_eq_iff that(1) that(2))
  have I1_tgt_gamma: \<open>I1.tgt.\<Gamma> = MorphImg \<phi> \<Gamma>\<close>    
    using I1.tgt_Gamma_eq_Morph_img by auto
  interpret sigma: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<sigma>
    apply (intro I1.tgt.inj_morph_img_isomorphism[simplified I1_tgt_gamma])
    subgoal by (simp add: inj_onI)    
    by (simp add: IS2.injection_to_ZF_exist)
    
  have sigma_phi: \<open>\<sigma> \<circ> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> 
    by (intro bijections_I particular_struct_bijection_1_comp
        I1.particular_struct_bijection_1_axioms
        sigma.particular_struct_bijection_1_axioms
          )

  have sigma_phi_img: \<open>MorphImg (\<sigma> \<circ> \<phi>) \<Gamma> \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>    
    using sigma_phi by blast

  have sigma_phi_morph: \<open>\<sigma> \<circ> \<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg (\<sigma> \<circ> \<phi>) \<Gamma>\<^esub>\<close>    
    by (meson bijections1_are_morphisms sigma_phi)

  show \<open>?thesis\<close>
  proof (simp)
    fix y  
    obtain P\<^sub>1:           
              \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P\<^sub>1 \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
      using identity_pred_E[OF assms(1)] by metis
    obtain P\<^sub>2: 
              \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P\<^sub>2 \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close> 
      using identity_pred_E[OF assms(2)] by metis
    note Q1 = P\<^sub>1[OF sigma_phi_img,of \<open>\<sigma> \<circ> \<phi>\<close>,OF sigma_phi_morph]
    note Q2 = P\<^sub>2[OF sigma_phi_img,of \<open>\<sigma> \<circ> \<phi>\<close>,OF sigma_phi_morph]
    show \<open>P\<^sub>1 (MorphImg \<sigma> (MorphImg \<phi> \<Gamma>)) y = P\<^sub>2 (MorphImg \<sigma> (MorphImg \<phi> \<Gamma>)) y\<close>
      apply (intro iffI)
      subgoal using Q1[of \<open>y\<close>] Q2(1) by simp
      subgoal using Q2[of \<open>y\<close>] Q1(1) by simp
      done
  qed
qed


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_img_comp_1[simp]: 
  \<open>MorphImg \<phi>\<^sub>1 \<circ> MorphImg \<phi>\<^sub>2 = MorphImg (\<phi>\<^sub>1 \<circ> \<phi>\<^sub>2)\<close>
  by (intro ext ; simp)


context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  As expected, an identity predicate is capable of ``picking'' the
  correspondent of \<open>x\<close> under an isomorphism:
  \<close>
text_raw \<open>\par\<close>   
lemma identity_respects_isomorphisms:
  assumes 
    \<open>identity_pred \<Gamma> P x\<close>
    \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE('p\<^sub>1)\<^esub>\<close>  
  shows \<open>identity_pred (MorphImg \<phi> \<Gamma>) P (\<phi> x)\<close>
proof -  
  obtain \<phi>\<^sub>1 where  
      A: \<open>particular_struct \<Gamma>\<close>
        \<open>\<phi>\<^sub>1 \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> particulars \<Gamma>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
      \<open>x \<in> particulars \<Gamma>\<close>
    using identity_pred_E[OF assms(1)] by metis
  have x_E[simp,intro!]: \<open>x \<in> \<E>\<close> using A(4) by simp
  interpret I1: particular_struct \<open>\<Gamma>\<close> using A(1) by simp
  interpret I2: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close> 
    using assms(2) by blast
  have B: \<open>I2.tgt.\<Gamma> = MorphImg \<phi> \<Gamma>\<close>    
    apply (intro particular_struct_eqI)
    by (simp_all only: I2.tgt.\<Gamma>_def particular_struct.simps)  
  obtain f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close> where f: \<open>inj f\<close> 
    using I2.tgt.injection_to_ZF_exist by blast
  have \<open>f \<in> BijMorphs1\<^bsub>MorphImg \<phi> \<Gamma>,TYPE(ZF)\<^esub>\<close>
    apply (auto)
    apply (intro I2.tgt.inj_morph_img_isomorphism[simplified B])
    subgoal by (meson f injD inj_onI)    
    using inj_on_id by blast
  then have C: \<open>BijMorphs1\<^bsub>MorphImg \<phi> \<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close> by blast  
  have D: \<open>\<phi>' \<circ> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> if
    as: \<open>\<phi>' \<in> BijMorphs1\<^bsub>MorphImg \<phi> \<Gamma>,TYPE(ZF)\<^esub>\<close> for \<phi>'
  proof -
    interpret II1: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<open>\<phi>'\<close>
      using as by blast
    show \<open>?thesis\<close>
      apply (intro bijections_I)
      apply (rule particular_struct_bijection_1_comp)
      subgoal        
        by (simp only: I2.particular_struct_bijection_1_axioms)      
      using II1.particular_struct_bijection_1_axioms by blast
  qed
  show \<open>?thesis\<close>
  proof (intro identity_pred_I C)
    show \<open>\<phi> x \<in> I2.tgt.endurants\<close>
      using A(4) by blast
    fix \<Gamma>' \<phi>' y'
    assume as3: \<open>\<Gamma>' \<in> IsoModels\<^bsub>MorphImg \<phi> \<Gamma>,TYPE(ZF)\<^esub>\<close> 
                \<open>\<phi>' \<in> Morphs\<^bsub>MorphImg \<phi> \<Gamma>,\<Gamma>'\<^esub>\<close>
    then have AA: \<open>\<phi>' \<circ> \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>      
      using I2.particular_struct_morphism_axioms 
            particular_struct_morphism_comp 
      by blast  
    interpret phi'_phi: particular_struct_morphism \<open>\<Gamma>\<close> \<open>\<Gamma>'\<close> \<open>\<phi>' \<circ> \<phi>\<close>
      using AA[THEN morphs_D] by simp
      
    obtain \<phi>\<^sub>1 where 
      phi1: \<open>\<phi>\<^sub>1 \<in> BijMorphs1\<^bsub>MorphImg \<phi> \<Gamma>,TYPE(ZF)\<^esub>\<close> 
            \<open>\<Gamma>' = MorphImg \<phi>\<^sub>1 (MorphImg \<phi> \<Gamma>)\<close>
      using as3(1) by blast
    have BB: \<open>\<Gamma>' = MorphImg (\<phi>\<^sub>1 \<circ> \<phi>) \<Gamma>\<close> using phi1(2) by simp
    have CC: \<open>\<phi>\<^sub>1 \<circ> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
      apply (simp ; safe)
      subgoal 
        apply (rule comp_inj_on)
        subgoal using I2.morph_is_injective by auto
        by (metis I2.morph_is_surjective particular_struct_bijection_1_def
                  particular_struct_injection.morph_is_injective 
                  bijections_D
                  phi1(1) ufo_particular_theory_sig.\<Gamma>_simps(2))        
      using inj_on_id by blast
    interpret phi1_phi: particular_struct_bijection_1 \<Gamma> \<open>\<phi>\<^sub>1 \<circ> \<phi>\<close> 
      using CC by blast

    have Gamma'_isomodel: \<open>\<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
      by (intro isomorphic_models_I[of \<open>\<phi>\<^sub>1 \<circ> \<phi>\<close>] BB CC)

    have phi1_comp_phi_morphs[simp,intro!]: \<open>\<phi>\<^sub>1 \<circ> \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>      
      using BB CC bijections1_are_morphisms by fastforce

    have ex_morph: \<open>\<exists>\<phi>\<in>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>. \<Gamma>' = MorphImg \<phi> \<Gamma>\<close>      
      using BB CC by blast
    
    show \<open>P \<Gamma>' y' = (\<forall>z \<in> I2.tgt.endurants. (y' = \<phi>' z) = (z = \<phi> x))\<close>
    proof (intro iffI ballI  ; simp?)
      fix z
      assume as4: \<open>P \<Gamma>' (\<phi>' z)\<close> \<open>z \<in> I2.tgt.\<P>\<close> \<open>y' = \<phi>' z\<close>

      have inv_z_dom[simp]: \<open>I2.inv_morph z \<in> \<E>\<close> 
        using I2.phi_inv_scope as4(2) by auto
      have inv_z[simp]: \<open>\<phi> (I2.inv_morph z) = z\<close>
        by (simp add: as4(2))
      note R1= A(3)[THEN iffD1, rule_format,OF _ phi1_comp_phi_morphs
                  ,where z=\<open>I2.inv_morph z\<close>,simplified
                  ,OF ex_morph as4(1),simplified]                     
                  
      note R2= A(3)[THEN iffD1, rule_format,OF _ AA,simplified
                , OF ex_morph as4(1),of \<open>I2.inv_morph z\<close>,
                   simplified]
      have R3: \<open>\<phi>' z = \<phi>\<^sub>1 z\<close>  using R1 R2 by simp
      note as4_1 =  as4[simplified R3]
      show \<open>z = \<phi> x\<close>
        using as4_1 A(3)[THEN iffD1,OF _ _ as4_1(1),rule_format
              , simplified,OF ex_morph,of _ ] 
        using R2 by auto        
    next
      fix z
      assume as4: \<open>P \<Gamma>' y'\<close> \<open>\<phi> x \<in> I2.tgt.\<P>\<close> \<open>z = \<phi> x\<close>
      note R1 = A(3)[simplified,THEN iffD1,OF ex_morph,rule_format
                  ,OF _ as4(1)]
      show \<open>y' = \<phi>' (\<phi> x)\<close>
        using R1 A(3) 
        using AA Gamma'_isomodel as4(1) by auto
    next
      assume \<open>\<forall>z \<in> I2.tgt.\<P>. y' = \<phi>' z \<longleftrightarrow> z = \<phi> x\<close>
      then have as4: \<open>y' = \<phi>' z \<longleftrightarrow> z = \<phi> x\<close> if \<open>z \<in> I2.tgt.\<P>\<close> for z
        using that by metis
      note R1 = A(3)[THEN iffD2,of \<Gamma>' _ y',rule_format,simplified,
                OF ex_morph,of \<open>\<phi>' \<circ> \<phi>\<close>,simplified,
                OF phi'_phi.particular_struct_morphism_axioms]
      note R2 = A(3)[THEN iffD2,of \<Gamma>' _ y',rule_format,simplified,
                OF ex_morph,of \<open>\<phi>\<^sub>1 \<circ> \<phi>\<close>,simplified 
                , simplified
                 phi1_phi.particular_struct_morphism_axioms[simplified,
                   simplified phi1(2)[symmetric]],
                 simplified]
      note R3 = as4[simplified  I2.morph_is_surjective[symmetric]]
      note R1 R2 R3[of \<open>\<phi> z\<close>,simplified]           
  
      note I2.morph_is_surjective[symmetric]
      have R5: \<open>\<phi> z = \<phi> x \<longleftrightarrow> z = x\<close> if \<open>z \<in> \<E>\<close> for z
        using that \<open>x \<in> \<E>\<close> I2.morph_is_injective inj_onD 
        by (metis \<Gamma>_simps(2))
      show \<open>P \<Gamma>' y'\<close>
        apply (intro R1 )
        subgoal premises P for z
          apply (rule as4[of \<open>\<phi> z\<close>,simplified R5[OF P]])
          using P 
          by (simp add: I2.morph_preserves_particulars)
        done
    qed
  qed          
qed
   
end

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred:
  fixes 
     P x and \<phi> :: \<open>'p \<Rightarrow> ZF\<close>
  assumes \<open>identity_pred \<Gamma> P x\<close> \<open>inj_on \<phi> \<P>\<close>
  shows \<open>P (MorphImg \<phi> \<Gamma>) y \<longleftrightarrow> y = \<phi> x\<close>
proof -
  obtain A: 
    \<open>\<And>\<Gamma>' \<phi> y. 
      \<lbrakk> \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;
        \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<rbrakk> \<Longrightarrow>
       P \<Gamma>' y \<longleftrightarrow> (\<forall>z\<in>particulars \<Gamma>. (y = \<phi> z) = (z = x))\<close>
    \<open>x \<in> particulars \<Gamma>\<close>
    using identity_pred_E[OF assms(1)] by metis
  have B: \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    apply (simp ; intro conjI)
    subgoal using assms(2)[THEN inj_on_subset,simplified] by simp
    using inj_on_id by blast
  then interpret I: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close> by simp
  have C: \<open>MorphImg \<phi> \<Gamma> \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    by (intro isomorphic_models_I[of \<open>\<phi>\<close>] B ; simp)
  have D: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close>    
    using I.particular_struct_morphism_axioms by blast    
  show \<open>?thesis\<close>
    apply (intro iffI ; simp add: A(1)[OF C D,of y])
    subgoal 
      using assms(1) identity_pred_E' by fastforce
    subgoal
      by (metis C D I.morph_is_injective A inj_onD)
    done
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_I1:
  fixes P and x
  assumes 
    \<open>x \<in> \<E>\<close>
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> \<E>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
  shows \<open>identity_pred \<Gamma> P x\<close>
proof -   
  have A: \<open>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close>
  proof -
    obtain \<phi> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>inj \<phi>\<close> 
      using injection_to_ZF_exist by blast
    then have \<open>inj_on \<phi> \<P>\<close> 
      using inj_on_subset \<open>inj \<phi>\<close> by blast
    have \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
      apply (intro \<open>inj_on \<phi> \<P>\<close> inj_morph_img_BijMorphs)
      using  inj_on_id by blast
    then show \<open>?thesis\<close> by blast
  qed              
  
  show \<open>?thesis\<close>
    apply (intro identity_pred_I[OF A])
    using assms by auto     
qed


lemma \<^marker>\<open>tag (proof) aponly\<close> identity_pred_eqI:
  assumes 
    \<open>identity_pred \<Gamma> P x\<close>
    \<open>\<sigma> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> 
    \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<sigma> \<Gamma>\<^esub>\<close>    
  shows \<open>P (MorphImg \<sigma> \<Gamma>) y \<longleftrightarrow> (\<forall>z \<in> \<E>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
proof -
  have ps[simp]: \<open>particulars \<Gamma> = \<E>\<close> by simp
  obtain A: \<open>x \<in> \<E>\<close>
    \<open>\<And>\<Gamma>' \<phi> y. \<lbrakk> 
          \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ;  
          \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>
         \<rbrakk> \<Longrightarrow>  P \<Gamma>' y \<longleftrightarrow> (\<forall>z \<in> \<E>. y = \<phi> z \<longleftrightarrow> z = x)\<close>
    using assms(1)[THEN identity_pred_E,simplified ps] 
    by metis
  have B: \<open>MorphImg \<sigma> \<Gamma> \<in> IsoModels\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> 
    using assms(2) by blast
  show \<open>?thesis\<close>
    using A B assms(3)
    by blast
qed

end

end