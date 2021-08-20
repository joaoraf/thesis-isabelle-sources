section \<open>Universal Trimming Operation\<close>

theory Trimming
  imports Instantiation "../ParticularStructures/Permutability"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The basic intuition behind our characterization of sortality is 
  that the main ``function'' of a universal (a concept) is to
  abstract away details from the reality. In this sense, an
  universal is not characterized as something that adds
  something to reality, e.g. it does not ``supply'' an identity
  principle, as much as something that subtracts from reality.

  As abstract entities, universals are completely determined by
  their formal properties. More specifically, they are 
  completely determined by their  application conditions.
  In other words, if the application conditions
  of two universals are logically equivalent, then they
  are identical. 

  Moreover, since there can be many distinct application
  conditions that are logically equivalent, we can say that
  UFO universals are determined by the instantiation relation
  denoted by this class of conditions.

  What do we mean, however, when we refer to an ``application
  condition''? At first glance, it could be simply a formal 
  logic expression denoting an intensional instantiation 
  relation, e.g. a particular \<open>x\<close> is an instance of \<open>U\<close> in
  the possible world \<open>w\<close> if and only if such and such condition
  is true. 

  However, this approach suffers from the sames issues
  regarding the reliance on the existence of languages that
  identification predicates do:

  \begin{itemize}
    \item it implies that universals can only be understood
          in an ontology that also presupposes the existence
          of formal languages\footnote{note that this
          is not the same as affirming that we need a 
          language to talk about an ontology};
    \item it is too weak, in the sense that even if
          a universal's application condition can be
          expressed in a simple and clear way, this approach
          allows also the same universal to be characterized
          by expressions that are much more complex or confusing;
    \item it has more of a descriptive role than an
          explanatory role: given a choice of expression,
          it might not be clear why that choice was made,
          since many others could be equally valid.    
  \end{itemize}

  Ideally, we should characterize universals by means of the 
  properties that are already present in the structure of UFO
  particular models, without introducing formal languages in 
  the domain of discourse. One alternative is to characterize
  universals by their extensions in each possible world,
  but such a characterization could hardly be considered 
  informative or explanatory, since we don't usually grasp
  universals by listing their potential instances.  

  Fortunately, UFO already provides a notion that gives us
  an adequate alternative: the characterizing relation
  between substantial universals and moment universals.
  Given a substantial universal \<open>U\<close> and a moment universal
  \<open>u\<close>, we say that \<open>U\<close> is characterized by \<open>u\<close>, or that
  \<open>u\<close> characterizes \<open>U\<close>, if and only if whenever a substantial
  instantiates \<open>U\<close>, it also bears a moment that instantiates
  \<open>u\<close>. For example, the substantial universal \emph{human being}
  is characterized by the moment universal \emph{skin color}, i.e.
  every human being has a skin color. The set of all characterizing
  universals of a substantial universal \<open>U\<close> is called the 
  characterizing set of \<open>U\<close>.

  Characterizing sets are not necessarily unique, given a
  a particular structure and an instantiation relation. However,
  a case in which two distinct substantial universals (having distinct 
  instantiation relations) have the same characterizing
  set can be considered a form of descriptive incompleteness:
  the fact that a person is able to distinguish these two
  universals means that at least one extra property could be
  added to the ontology, in the form of an extra moment universal
  and its instances, that can explain the distinction.
  
  Thus, if we assume that characterizing sets are unique, 
  we can invert their role, from being a description of a 
  universal's properties to being a determiner of the 
  universal instances. In other words, the characterizing set
  can play the role of an application condition: two 
  substantial universals are considered identical if and only
  if they have the same characterizing sets, and a substantial
  is considered an instance of a universal \<open>U\<close> in a world \<open>w\<close>
  if and only if it bears, in \<open>w\<close>, at least one moment 
  corresponding to each moment universal in the characterizing
  set of \<open>U\<close>.
  
  With unique characterizing sets as application conditions,
  we can also show how the determining property of a 
  substantial universal, i.e. its application condition, 
  explains the way in which a universal ``substracts'' from
  the reality. The idea is that the characterizing set determines
  the assumptions one is allowed to make, given the knowledge that
  a particular instantiates a certain universal. In other words,
  the characterizing set represents the ``filter'' that a universal
  imposes on reality.

  For example, consider the universals \emph{physical object} and
  \emph{piece of wood}: since pieces of wood are also physical objects,
  every moment universal that characterizes physical objects also
  characterize pieces of wood (subsumption if reducible to the subset
  relation between characterizing sets). However, not all characterizing
  universal of pieces of wood are also characteze physical objects.
  For example, the universal \emph{wood vein pattern} characterizes pieces
  of wood, but not physical objects, since not all physical objects have
  a wood vein pattern. Thus, when a piece of wood is seen through the
  filter of the physical object universal, the wood vein pattern property
  is abstracted away.

  In this section, we define formally two concepts that capture this
  abstraction process: detailing moments of a substantial universal and
  the trimming of a particular structure by a substantial universal.
     
\<close>
text_raw \<open>\par\<close>
context instantiation_sig
begin

text_raw \<open>\subsection[Detailing moments]{Detailing moments\isalabel{subsec:detailing-moments}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The detailing moments of a substantial universal \<open>U\<close> are those moments that
  represent details that are abstracted away by \<open>U\<close>. Any moment \<open>m\<close> that inheres 
  in an instance \<open>x\<close> of \<open>U\<close> is either an instance of a characterizing universal of
  \<open>U\<close> or it is not. The detailing moments of \<open>U\<close> are comprised of precisely the later
  and of the moments that inhere on them.
  Formally, we have:
\<close>
text_raw \<open>\par\<close>  
inductive_set detailingMoments :: \<open>'u \<Rightarrow> 'p set\<close> (\<open>\<Delta>\<^bsub>_\<^esub>\<close> [999] 1000) for U 
  where
    non_char_moments:
      \<open>\<lbrakk> U \<in> \<U>\<^sub>\<S> ; x \<in> Insts U ; y \<triangleleft> x ; 
       \<forall>w u. y \<Colon>\<^bsub>w\<^esub> u \<longrightarrow> \<not> char_by U u 
      \<rbrakk> \<Longrightarrow> y \<in> \<Delta>\<^bsub>U\<^esub>\<close>
  | sub_moments: \<open>\<lbrakk> x \<in> \<Delta>\<^bsub>U\<^esub> ; y \<triangleleft>\<triangleleft> x \<rbrakk> \<Longrightarrow> y \<in> \<Delta>\<^bsub>U\<^esub>\<close>  

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given a particular structure with set of possible worlds \<open>\<W>\<close>, 
  we call the set of possible worlds \emph{trimmed by} \<open>U\<close>, 
  written as \<open>trim_worlds U\<close>, the set composed by the each
  possible world minus the detailing moments of \<open>U\<close>:
\<close>
text_raw \<open>\par\<close>
definition \<open>trim_worlds U \<equiv> { w - \<Delta>\<^bsub>U\<^esub> | w . w \<in> \<W> }\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_worlds_I:
  assumes \<open>w \<in> \<W>\<close> \<open>w' = w - \<Delta>\<^bsub>U\<^esub>\<close>
  shows \<open>w' \<in> trim_worlds U\<close>
  using assms by (auto simp: trim_worlds_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_worlds_E:
  assumes \<open>w' \<in> trim_worlds U\<close>
  obtains w where \<open>w \<in> \<W>\<close> \<open>w' = w - \<Delta>\<^bsub>U\<^esub>\<close>
  using assms by (auto simp: trim_worlds_def)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Similarly, we call the inherence relation \emph{trimmed by} \<open>U\<close>,
  written as \<open>trim_inheres_in U\<close>, the restriction of the
  inherence relation to those particulars that are not
  detailing moments of \<open>U\<close>, and, proceeding the same way,
  we can build restricted forms of all of the formal relations
  of the UFO theory of particulars:
\<close>
text_raw \<open>\par\<close>
definition \<open>trim_inheres_in U x y \<equiv> x \<triangleleft> y \<and> x \<notin> \<Delta>\<^bsub>U\<^esub> \<and> y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_inheres_in_I:
  assumes \<open>x \<triangleleft> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  shows \<open>trim_inheres_in U x y\<close>
  using assms by (auto simp: trim_inheres_in_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_inheres_in_E:
  assumes \<open>trim_inheres_in U x y\<close>
  obtains \<open>x \<triangleleft> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  using assms by (auto simp: trim_inheres_in_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_inheres_in_D:
  assumes \<open>trim_inheres_in U x y\<close>
  shows \<open>x \<triangleleft> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  using assms by (auto simp: trim_inheres_in_def)

definition \<open>trim_assoc_quale U x q \<equiv> x \<leadsto> q \<and> x \<notin> \<Delta>\<^bsub>U\<^esub>\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_assoc_quale_I:
  assumes \<open>x \<leadsto> q\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> 
  shows \<open>trim_assoc_quale U x q\<close>
  using assms by (auto simp: trim_assoc_quale_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_assoc_quale_E:
  assumes \<open>trim_assoc_quale U x q\<close>
  obtains \<open>x \<leadsto> q\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> 
  using assms by (auto simp: trim_assoc_quale_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_assoc_quale_D:
  assumes \<open>trim_assoc_quale U x q\<close>
  shows \<open>x \<leadsto> q\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> 
  using assms by (auto simp: trim_assoc_quale_def)

definition \<open>trim_towards U x y \<equiv> 
  x \<longlongrightarrow> y \<and> x \<notin> \<Delta>\<^bsub>U\<^esub> \<and> y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_towards_I:
  assumes \<open>x \<longlongrightarrow> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  shows \<open>trim_towards U x y\<close>
  using assms by (auto simp: trim_towards_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_towards_E:
  assumes \<open>trim_towards U x y\<close>
  obtains \<open>x \<longlongrightarrow> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  using assms by (auto simp: trim_towards_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_towards_D:
  assumes \<open>trim_towards U x y\<close>
  shows \<open>x \<longlongrightarrow> y\<close> \<open>x \<notin> \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  using assms by (auto simp: trim_towards_def)

definition \<open>trim_quality_spaces U \<equiv> 
    { Q | Q x q . Q \<in> \<Q>\<S> \<and> q \<in> Q 
                  \<and> trim_assoc_quale U x q }\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_quality_spaces_I:
  assumes \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close> \<open>trim_assoc_quale U x q\<close>
  shows \<open>Q \<in> trim_quality_spaces U\<close>
  using assms by (auto simp: trim_quality_spaces_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_quality_spaces_E:
  assumes \<open>Q \<in> trim_quality_spaces U\<close>
  obtains q x where \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close> \<open>trim_assoc_quale U x q\<close>
  using assms by (auto simp: trim_quality_spaces_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_quality_spaces_subset: \<open>trim_quality_spaces U \<subseteq> \<Q>\<S>\<close>  
  by (simp add: trim_quality_spaces_def)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Using the restricted versions of the formal elements of \<open>\<Gamma>\<close>, we can
  define the \emph{trimming operation}: given a particular structure \<open>\<Gamma>\<close> and
  a universal \<open>U\<close>, we call \<open>\<Gamma>\<close> trimmed by \<open>U\<close>, written as \<open>trim U\<close>, the
  particular structure constructed by removing the detailing moments of \<open>U\<close>
  from \<open>\<Gamma>\<close>, leaving it otherwise the same: 
\<close>
text_raw \<open>\par\<close>
definition \<open>trim U = \<lparr>
    ps_quality_spaces = trim_quality_spaces U,
    ps_worlds = trim_worlds U,
    ps_inheres_in = trim_inheres_in U,
    ps_assoc_quale = trim_assoc_quale U,
    ps_towards = trim_towards U
  \<rparr>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given a universal \<open>U\<close>, we use the expression 
  \<open>trim_non_permutables U\<close> to denote the particulars that are non-permutable
  in \<open>\<Gamma>\<close> trimmed by \<open>U\<close>:
\<close>
text_raw \<open>\par\<close>
abbreviation \<open>trim_non_permutables U \<equiv>
  ufo_particular_theory_sig.non_permutables 
    (trim_worlds U) 
    (trim_inheres_in U) 
    (trim_quality_spaces U) 
    (trim_assoc_quale U) 
    (trim_towards U)\<close>

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_simps:
  \<open>ps_quality_spaces (trim U) = trim_quality_spaces U\<close>
  \<open>ps_worlds (trim U) = trim_worlds U\<close>
  \<open>ps_inheres_in (trim U) = trim_inheres_in U\<close>
  \<open>ps_assoc_quale (trim U) = trim_assoc_quale U\<close>
  \<open>ps_towards (trim U) = trim_towards U\<close>
  by (auto simp: trim_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_particulars[simp]:
   \<open>possible_worlds_sig.\<P> (ps_worlds (trim U)) = \<P> - \<Delta>\<^bsub>U\<^esub>\<close>
  apply (auto simp: trim_simps possible_worlds_sig.\<P>_def)
  subgoal by (metis Diff_iff trim_worlds_E)
  subgoal using trim_worlds_E by auto
  subgoal using trim_worlds_def by auto
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_particulars_1[simp]:
   \<open>possible_worlds_sig.\<P> (trim_worlds U) = \<P> - \<Delta>\<^bsub>U\<^esub>\<close>
  using trim_particulars[simplified trim_simps] .


lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_moments[simp]: 
    \<open>inherence_sig.\<M> (ps_inheres_in (trim U)) = \<M> - \<Delta>\<^bsub>U\<^esub>\<close>
  apply (auto simp: inherence_sig.\<M>_def trim_simps)
  subgoal G1 using trim_inheres_in_D(1) by blast
  subgoal G2 by (simp add: trim_inheres_in_def)
  subgoal for y x
    apply (intro exI[of _ x] trim_inheres_in_I ; simp?)
    apply (rule ccontr ; simp)
    subgoal premises P
      using P(3,1,2) 
      apply (induct x arbitrary: y rule: detailingMoments.induct ; simp?)
      subgoal G3_1 premises P for x\<^sub>1 x\<^sub>2 x\<^sub>3
        supply R1 = tranclp.intros(1)[of \<open>(\<triangleleft>)\<close>,OF P(6)]      
        supply R2 = tranclp.intros(2)[OF R1 P(3)]
        supply R3 = detailingMoments.intros(2)[
                      of x\<^sub>1 U x\<^sub>3,OF _ R2, THEN P(5)[THEN notE]]
        supply R4 = detailingMoments.intros(1)[OF P(1,2,3,4)]
        apply (rule R3)
        using detailingMoments.intros(2)[OF R4 R1] P(5) by simp
      subgoal G3_2 premises P for x\<^sub>1 x\<^sub>2 x\<^sub>3
        supply R1 = tranclp_trans[OF tranclp.intros(1)[of \<open>(\<triangleleft>)\<close>, OF P(5)] P(3)]
        using detailingMoments.intros(2)[OF P(1) R1] P(4) by simp
      done
    done
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_moments_1[simp]: 
  \<open>inherence_sig.\<M> (trim_inheres_in U) = \<M> - \<Delta>\<^bsub>U\<^esub>\<close>
  using trim_moments[simplified trim_simps] .


end

context iso_universals
begin

notation \<^marker>\<open>tag aponly\<close> detailingMoments (\<open>\<Delta>\<^bsub>_\<^esub>\<close> [999] 1000) 

context
  fixes \<phi> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close> and \<Gamma>'
  assumes A: \<open>particular_struct_bijection_1 \<Gamma> \<phi>\<close>
begin

interpretation phi: particular_struct_bijection_1 \<Gamma> \<phi> using A by simp

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_tgt_iof_1:
  assumes \<open>x \<in> \<phi> ` \<P>\<close> \<open>w \<in> ((`) \<phi>) ` \<W>\<close>
  shows
  \<open>iso_instantiation_sig.iof phi.\<W>\<^sub>\<phi> phi.img_inheres_in phi.tgt.\<Q>\<S>
       phi.img_assoc_quale phi.img_towards zf_iof x w u \<longleftrightarrow>
    (\<exists>x\<^sub>1 w\<^sub>1. x = \<phi> x\<^sub>1 \<and> w = \<phi> ` w\<^sub>1 \<and> x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u)\<close>
proof -
  obtain x\<^sub>1 where x1[simp]: \<open>x\<^sub>1 \<in> \<P>\<close> \<open>x = \<phi> x\<^sub>1\<close> using assms(1) by blast
  obtain w\<^sub>1 where w1[simp]: \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w = \<phi> ` w\<^sub>1\<close> using assms(2) by blast 
  obtain f\<^sub>1 :: \<open>'p \<Rightarrow> ZF\<close> where f1: \<open>inj f\<^sub>1\<close> 
    using phi.src.injection_to_ZF_exist by blast
  obtain f\<^sub>2 :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close> where f2: \<open>inj f\<^sub>2\<close> 
    using phi.tgt.injection_to_ZF_exist by blast
  have A: \<open>ufo_particular_theory_sig.\<Gamma> ((`) \<phi> ` phi.src.\<W>) phi.img_inheres_in
            phi.tgt.\<Q>\<S> phi.img_assoc_quale phi.img_towards =
            MorphImg \<phi> \<Gamma>\<close>    
    using phi.morph_image_tgt_struct phi.morph_image_worlds_src by auto

  have C[simp]: \<open>\<phi> ` w\<^sub>2 = \<phi> ` w\<^sub>1 \<longleftrightarrow> w\<^sub>2 = w\<^sub>1\<close> if \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>2 \<in> \<W>\<close> for w\<^sub>1 w\<^sub>2
    using that phi.phi_inv_phi_world by (metis \<Gamma>_simps(2))
  have D[simp]: \<open>possible_worlds_sig.\<P> ((`) \<phi> ` phi.src.\<W>) = \<phi> ` \<P>\<close>    
    using phi.morph_image_worlds_src phi.morph_is_surjective by auto
  have E: \<open>inj_on (f \<circ> \<phi>) \<E> \<longleftrightarrow> inj_on f (\<phi> ` \<E>)\<close> for f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close>
    using inj_on_imageI[of f \<phi> \<E>] comp_inj_on[OF phi.morph_is_injective[simplified]]
    by metis
  have F: \<open>f ` \<phi> ` w\<^sub>2 = (\<lambda>x. f (\<phi> x)) ` w\<^sub>2\<close> for f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close> and w\<^sub>2
    by auto 
  have G[simp,intro!]: \<open>inj_on f\<^sub>2 (\<phi> ` \<E>)\<close>
    using f2 inj_on_subset by auto
  have f_phi_ext: \<open>f \<circ> \<phi> \<in> extensional \<P>\<close> if 
    as: \<open>f \<in> extensional (\<phi> ` \<P>)\<close> 
      for f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close>
    using as phi.morphism_extensional apply (simp add: extensional_def)
    apply safe    
    using phi.undefined_not_in_img by auto
  have H: \<open>MorphImg (f \<circ> \<phi>) \<Gamma> = MorphImg f (MorphImg \<phi> \<Gamma>)\<close> for f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close>
    apply (subst phi.src.morph_img_comp[of f \<phi>,symmetric])
    apply (auto )
    sorry
  show ?thesis
    apply (intro iffI iso_instantiation_sig.iof_I[OF inj_on_subset[OF f2]]
      ; simp only: phi.morph_image_worlds_src D
      ; elim iso_instantiation_sig.iof_E1 exE conjE imageE
      ; hypsubst_thin? ; (simp only: A D)?
      ; simp)
    subgoal premises P for f w\<^sub>2      
      apply (intro exI[of _ x\<^sub>1] ; simp? ; intro exI[of _ w\<^sub>2] ; simp)
      apply (intro iof_I[of \<open>f \<circ> \<phi>\<close>,simplified E,OF P(1), of w\<^sub>2 x\<^sub>1 u,OF P(5),
            OF,simplified])
      subgoal G1
        using P(2)
        sorry
      subgoal G2 by (intro f_phi_ext P)        
      apply (simp add: image_def ; safe)      
      using P(4) by blast
    subgoal premises P for x\<^sub>2 w\<^sub>2 f
      using 
        phi.invariant_under_isomorphisms_B[OF iso_invariant_iof_predicate_axioms
          , simplified,OF P(1) _ P(3,2),OF G,
          THEN iffD1,OF P(4)] 
      .
    done
qed

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_tgt_iof_iff:
  \<open>iso_instantiation_sig.iof phi.\<W>\<^sub>\<phi> phi.img_inheres_in phi.tgt.\<Q>\<S>
       phi.img_assoc_quale phi.img_towards zf_iof x w u \<longleftrightarrow>
    (\<exists>x\<^sub>1 w\<^sub>1. x = \<phi> x\<^sub>1 \<and> w = \<phi> ` w\<^sub>1 \<and> x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u)\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof -  
  have A0: \<open>x \<in> \<phi> ` \<P> \<and> w \<in> ((`) \<phi>) ` \<W>\<close> (is \<open>?A\<close>)
    if \<open>iso_instantiation_sig.iof phi.\<W>\<^sub>\<phi> phi.img_inheres_in phi.tgt.\<Q>\<S>
       phi.img_assoc_quale phi.img_towards zf_iof x w u \<or>
      (\<exists>x\<^sub>1 w\<^sub>1. x = \<phi> x\<^sub>1 \<and> w = \<phi> ` w\<^sub>1 \<and> x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u)\<close>  
    using that
    by (metis iso_instantiation_sig.iof_E1 phi.morph_image_simps(1)
          phi.morph_image_worlds_src phi.morph_preserves_particulars
          phi.world_preserve_img ufo_particular_theory_sig.\<Gamma>_simps(2)) 
  
  have A1: \<open>P \<longleftrightarrow> Q\<close> if \<open>A \<Longrightarrow> P \<longleftrightarrow> Q\<close> \<open>P \<or> Q \<Longrightarrow> A\<close>  for A  P Q
    using that by blast  
  show ?thesis
    apply (rule A1[where A = ?A and P = ?P and Q = ?Q])
    subgoal using phi_tgt_iof_1 by metis
    using A0 by simp
qed

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_src_iof_iff:
  \<open>iso_instantiation_sig.iof phi.\<W>\<^sub>\<phi> phi.img_inheres_in phi.tgt.\<Q>\<S>
       phi.img_assoc_quale phi.img_towards zf_iof (\<phi> x)(\<phi> ` w) u
   \<and> x \<in> \<P> \<and> w \<in> \<W>  \<longleftrightarrow> x \<Colon>\<^bsub>w\<^esub> u\<close> 
proof (simp only: phi_tgt_iof_iff ; intro iffI conjI ; (elim exE conjE)?)
  fix x\<^sub>1 w\<^sub>1
  assume as: \<open>x \<in> \<E>\<close> \<open>w \<in> \<W>\<close> \<open>\<phi> x = \<phi> x\<^sub>1\<close> \<open>\<phi> ` w = \<phi> ` w\<^sub>1\<close> \<open>x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u\<close>
  obtain A: \<open>x = x\<^sub>1\<close> \<open>w = w\<^sub>1\<close> 
    using that as(1,2,3,4) phi.morph_is_injective[simplified]          
    by (metis as(5) inj_onD inj_on_image_eq_iff iof_E1 
              worlds_are_made_of_particulars)
  show \<open>x \<Colon>\<^bsub>w\<^esub> u\<close> using A as by simp
next
  assume as: \<open>x \<Colon>\<^bsub>w\<^esub> u\<close>
  show \<open>x \<in> \<E>\<close> using as by blast
  show \<open>w \<in> \<W>\<close> using as by blast
  show \<open>\<exists>x\<^sub>1 w\<^sub>1. \<phi> x = \<phi> x\<^sub>1 \<and> \<phi> ` w = \<phi> ` w\<^sub>1 \<and> x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u\<close>
    by (intro exI[of _ x] exI[of _ w] as conjI ; simp)
qed
  
lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_inheres_in_tranclp:
  \<open>phi.tgt.inheresIn\<^sup>+\<^sup>+ x y \<longleftrightarrow> (\<exists>x\<^sub>1 y\<^sub>1. x\<^sub>1 \<triangleleft>\<triangleleft> y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close>
  apply (intro iffI)
  subgoal
    apply (rule exI[of _ \<open>phi.inv_morph x\<close>] ; rule exI[of _ \<open>phi.inv_morph y\<close>])
    apply (induct rule: tranclp.induct ; simp? ; intro conjI ; (elim conjE)?
          ; simp?)
    subgoal G1 for a b
      apply (intro phi.morph_reflects_inherence[of \<open>phi.inv_morph a\<close> 
                  \<open>phi.inv_morph b\<close>
            , THEN iffD1
            , THEN tranclp.intros(1)[of \<open>phi.src_inheres_in\<close>],simplified])
      subgoal G1_1 using phi.morph_image_def phi.phi_inv_scope by auto
      subgoal G1_2 using phi.phi_inv_scope by auto
      by (metis \<Gamma>_simps(3) phi.inv_inheres_in_reflects phi.tgt.inherence_scope)      
    subgoal G2 using phi.inv_morph_morph phi.tgt.inherence_scope by presburger
    subgoal G3 by auto
    subgoal G4 premises P for a b c
      apply (intro tranclp.intros(2)[OF P(3)])
      using P(1,2) 
        by (metis \<Gamma>_simps(3) phi.inv_inheres_in_reflects phi.tgt.inherence_scope)      
    using G3 by blast
  subgoal
    apply (elim exE conjE ; hypsubst_thin)
    subgoal for x\<^sub>1 y\<^sub>2
      apply (induct rule: tranclp.induct)
      subgoal G1 for a b
        apply (intro tranclp.intros(1))
        using phi.morph_reflects_inherence by auto
      subgoal G2 premises P for a b c
        apply (intro tranclp.intros(2)[OF P(2)])
        using P(3) phi.morph_reflects_inherence by auto
      done
    done
  done

interpretation inst2: 
  iso_universals \<open>phi.tgt.\<W>\<close> \<open>phi.tgt_inheres_in\<close> \<open>phi.tgt.\<Q>\<S>\<close>
        \<open>phi.tgt.assoc_quale\<close> \<open>phi.tgt.towards\<close> \<open>zf_iof\<close> \<open>TYPE('p\<^sub>1)\<close>
proof -
  have A: \<open>x\<^sub>2 \<Colon>\<^bsub>phi.inv_morph ` w\<^sub>2\<^esub> u\<close>
    if as: \<open>\<phi> x\<^sub>1 \<in> phi.tgt.\<M>\<close> \<open>x\<^sub>1 \<Colon>\<^bsub>w\<^sub>1\<^esub> u\<close>
          \<open>w\<^sub>2 \<in> phi.\<W>\<^sub>\<phi>\<close> \<open>\<phi> x\<^sub>2 \<in> w\<^sub>2\<close> \<open>x\<^sub>2 \<Colon>\<^bsub>w\<^sub>3\<^esub> u\<close> for x\<^sub>1 x\<^sub>2 w\<^sub>1 w\<^sub>2 w\<^sub>3 u
  proof -
    have AA: \<open>x\<^sub>1 \<in> \<E>\<close>  using iof_E[OF as(2)] by metis
    obtain g :: \<open>'p \<Rightarrow> ZF\<close> where  BB: \<open>inj_on g \<E>\<close> \<open>x\<^sub>2 \<in> \<E>\<close>
      using iof_E[OF as(5)] by blast

    interpret g: particular_struct_bijection_1 \<Gamma> g
      apply (intro inj_morph_img_isomorphism[of g] BB)
      using inj_on_id by blast
        
    have F: \<open>x\<^sub>1 \<in> \<M>\<close> using as(1) AA by auto
    then have G: \<open>u \<in> \<U>\<^sub>\<M>\<close> using as(2) by blast
    obtain H: \<open>u \<in> \<U>\<close> \<open>\<And>x w\<^sub>1 w\<^sub>2. \<lbrakk> x \<Colon>\<^bsub>w\<^sub>1\<^esub> u ; w\<^sub>2 \<in> \<W> ; x \<in> w\<^sub>2 \<rbrakk> \<Longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> u\<close>
      using moment_universals_are_rigid[OF G,THEN rigidE] by metis


    show \<open>x\<^sub>2 \<Colon>\<^bsub>phi.inv_morph ` w\<^sub>2\<^esub> u\<close>
      apply (rule H(2)[of _ w\<^sub>3,OF as(5)])
      subgoal  using \<Gamma>_simps(2) that(3) by blast      
      using BB(2) phi.tgt_world_corresp_inv_image that(3) that(4) by force
  qed

  interpret phi: iso_instantiation 
    where \<W> = phi.tgt.\<W> and
          inheresIn = phi.tgt_inheres_in and
          \<Q>\<S> = phi.tgt.\<Q>\<S> and
          assoc_quale = phi.tgt.assoc_quale and
          towards = phi.tgt.towards and
          zf_iof = zf_iof and
          Typ\<^sub>p = \<open>TYPE('p\<^sub>1)\<close>
    by (unfold_locales)

  show \<open>iso_universals phi.tgt.\<W> phi.tgt_inheres_in phi.tgt.\<Q>\<S>
        phi.tgt.assoc_quale phi.tgt.towards zf_iof\<close>
  apply (unfold_locales)
  subgoal
    apply (auto simp: instantiation_sig.\<U>\<^sub>\<S>_def instantiation_sig.\<U>\<^sub>\<M>_def
                  phi_tgt_iof_iff[simplified])
    subgoal premises P for U x\<^sub>1 x\<^sub>2 w\<^sub>1 w\<^sub>2
      supply R1 = \<U>\<^sub>\<M>_I[OF P(5)] 
      supply R2 = \<U>\<^sub>\<S>_I[OF P(4)] 
      supply R3 = substantial_moment_univs_separate[
                    simplified disjoint_eq_subset_Compl
                  , THEN subsetD,simplified,THEN notE]
      apply (rule R3[OF R2 R1])
      subgoal  
        using phi.tgt.\<S>_I[OF P(1,2)
                         , simplified phi.morph_image_substantials[simplified]]
        using P(4)[THEN iof_scope(1)]
        using phi.morph_image_substantials phi.morph_preserves_substantials by auto
      subgoal
        using P(3)
        using P(5)[THEN iof_scope(1)]
        using phi.morph_image_substantials phi.morph_preserves_substantials by auto
      done
    done
  subgoal for u
    apply (auto simp: instantiation_sig.\<U>\<^sub>\<S>_def instantiation_sig.\<U>\<^sub>\<M>_def
                  phi_tgt_iof_iff[simplified]
                  instantiation_sig.rigid_def
                  instantiation_sig.\<U>_def)
    subgoal for x\<^sub>1 w\<^sub>1 w\<^sub>2 x\<^sub>2 w\<^sub>3    
      apply (intro exI[of _ \<open>x\<^sub>2\<close>] conjI exI[of _ \<open>phi.inv_morph ` w\<^sub>2\<close>]
            ; simp)
      subgoal using A by metis
      done
    done
  done
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of detailing moments of a universal \<open>U\<close> is invariant under bijection morphisms
  (\<open>\<phi>\<close> is a bijection morphism for \<open>\<Gamma>\<close>):
\<close>
text_raw \<open>\par\<close>
lemma  detailingMoments_invariant: 
  \<open>inst2.detailingMoments U = \<phi> ` detailingMoments U\<close>
proof -
  have A: \<open>inst2.\<U>\<^sub>\<S> = \<U>\<^sub>\<S>\<close>
    apply (simp only: inst2.\<U>\<^sub>\<S>_def phi_tgt_iof_iff)    
    apply (auto ; (elim \<U>\<^sub>\<S>_E)?)
    subgoal for u x w by (intro \<U>\<^sub>\<S>_I[of x w] ; auto)
    subgoal for u x w apply (rule exI[of _ \<open>\<phi> x\<close>] ; intro conjI
            ; (rule exI[of _ \<open>\<phi> ` w\<close>] ; rule exI[of _ x])? 
            ; (intro conjI)?
            ; (rule exI[of _ w])? ; simp?)
      by auto 
    done
  have B: \<open>inst2.Insts U = \<phi> ` Insts U\<close>
    apply (intro set_eqI iffI ; (elim inst2.InstsE InstsE imageE)?
            ; simp only: phi_tgt_iof_iff
            ; (elim exE conjE)?
            ; hypsubst_thin)
    subgoal for _ _ x\<^sub>1 w\<^sub>1  by (intro imageI ; blast)
    subgoal for _ x w
      apply (intro inst2.InstsI[of _ \<open>\<phi> ` w\<close>])
      subgoal premises P
        apply (rule iof_E[OF P])
        subgoal premises Q
          using phi_src_iof_iff[of x w U,simplified Q(2,3), simplified simp_thms] P by simp
        done
      done
    done  
  have C: 
    \<open>phi.img_inheres_in y x \<longleftrightarrow> (\<exists>y\<^sub>1 x\<^sub>1. y\<^sub>1 \<triangleleft> x\<^sub>1 \<and> y = \<phi> y\<^sub>1 \<and> x = \<phi> x\<^sub>1)\<close> for x y
    by (metis (no_types, hide_lams) \<Gamma>_simps(2) \<Gamma>_simps(3) phi.I_img_eq_tgt_I
          phi.morph_image_E phi.morph_image_def phi.morph_image_iff 
          phi.morph_image_inheres_in_D(1) phi.morph_preserves_inherence_1 
          phi.morph_reflects_inherence phi.tgt.endurantI2)
  have D: \<open>inst2.\<U> = \<U>\<close>    
    using \<U>_def inst2.\<U>_def phi_tgt_iof_iff by auto
  have D1: \<open>w\<^sub>1 = w\<^sub>2\<close> if \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>2 \<in> \<W>\<close> \<open>\<phi> ` w\<^sub>1 = \<phi> ` w\<^sub>2\<close> for w\<^sub>1 w\<^sub>2
    using that phi.morph_is_injective[simplified] worlds_are_made_of_particulars
    by (meson inj_on_image_eq_iff)
  
  have E: \<open>inst2.char_by = char_by\<close>    
    apply (intro ext iffI char_by_I inst2.char_by_I ;
            elim char_by_E inst2.char_by_E ; (simp only: D)?)
    subgoal premises P for u\<^sub>1 u\<^sub>2 x w
      apply (rule P(4)[simplified phi_tgt_iof_iff
                      , THEN exE, simplified C
                      , of \<open>\<phi> x\<close> \<open>\<phi> ` w\<close> , simplified] 
            ; (elim exE conjE)?; hypsubst?)
      subgoal by (intro exI[of _ x] ; simp; intro exI[of _ w] ; simp add: P)
      subgoal premises Q for a x\<^sub>1 x\<^sub>2 x\<^sub>3 w\<^sub>1
        apply (rule P(1)[THEN iof_E])
        apply (rule Q(3)[THEN iof_E])
        subgoal premises T for f g
          supply R1 = phi.morph_is_injective[THEN inj_onD,simplified]
          supply R2 = Q(1)[THEN inherence_scope]
          supply R3 = R2[THEN conjunct1] R2[THEN conjunct2]
          supply R4 = Q(4)[THEN R1, OF T(7) R3(1)] Q(5)[THEN R1,OF T(2) R3(2)]
                      D1[OF T(3,8) Q(2)]
          using Q(1,3)[simplified R4[symmetric]] by blast
        done
      done
    subgoal premises P for u\<^sub>1 u\<^sub>2 x w
      using P(1) apply (simp only: phi_tgt_iof_iff)
      apply (elim exE conjE ; simp) 
      subgoal premises Q for x\<^sub>1 w\<^sub>1      
        using P(4)[OF Q(3)] apply (elim exE conjE)
        subgoal premises T for y
          apply (intro exI[of _ \<open>\<phi> y\<close>] conjI exI[of _ y] exI[of _ w\<^sub>1] T(2)
                ; (simp add: C)?)          
          using T Q P by blast
        done
      done
    done  
  have F: \<open>x\<^sub>1 = x\<close> if \<open>y\<^sub>1 \<triangleleft> x\<^sub>1\<close> \<open>\<phi> x\<^sub>1 = \<phi> x\<close> \<open>x \<in> \<P>\<close> for x\<^sub>1 x y\<^sub>1
    using phi.morph_is_injective[THEN inj_onD,simplified,OF that(2)]
        inherence_scope[OF that(1)] that(3) by metis
        
    
  show ?thesis
  apply (intro set_eqI iffI)
  subgoal for x
    apply (induct x rule: inst2.detailingMoments.inducts 
          ; (simp only: A B E phi_inheres_in_tranclp)?)
    subgoal for x y
      apply (simp only: C[of y x] ; elim exE conjE)
      apply (simp only: phi_tgt_iof_iff ; elim imageE ; simp ; intro imageI)
      subgoal premises P for x\<^sub>2 x\<^sub>3 x\<^sub>4    
        using P(7) apply (elim InstsE)
        subgoal premises Q for w
          using Q apply (elim iof_E)
          subgoal premises T for f
            supply R1 = F[OF P(3,6) T(2)]
            supply R2 = P(2)[simplified R1, rule_format, OF exI, OF conjI, 
                             OF _ exI,OF _ conjI] 
                        P(1,3,4,5)[simplified R1] Q[simplified R1] 
                        T[simplified R1] R1
            apply (intro detailingMoments.intros(1)[OF P(1) P(7) R2(3)] 
                    allI impI notI
                  ; elim char_by_E)
            subgoal premises O for w\<^sub>1 u
              using O(4)[OF \<open>x\<^sub>4 \<Colon>\<^bsub>w\<^esub> U\<close>] apply (elim exE conjE)
              subgoal premises Z for z                        
                by (metis O(1) O(4) R2(1) T(4) instantiation_sig.char_by_I)
              done
            done
          done
        done
      done
    subgoal for x y      
      apply (auto ; intro imageI 
            ; rule detailingMoments.intros(2)[of \<open>phi.inv_morph x\<close>] ; simp)
      subgoal by (metis \<Gamma>_simps(2) detailingMoments.cases inherence_scope
            inherence_sig.\<M>_E  particular_struct_bijection_1_def
            particular_struct_injection.inv_morph_morph 
            phi.particular_struct_bijection_1_axioms trans_inheres_in_scope)
      subgoal premises P for x\<^sub>1 x\<^sub>2 x\<^sub>3
        using P(4)
        by (metis \<Gamma>_simps(2) particular_struct_injection.inv_morph_morph 
                phi.particular_struct_injection_axioms trans_inheres_in_scope)
      done
    done
  subgoal 
    apply (elim imageE ; hypsubst_thin)
    subgoal for x
      apply (induct x rule: detailingMoments.inducts)
      subgoal for x\<^sub>1 x\<^sub>2
        apply (intro inst2.detailingMoments.intros(1)[of _ \<open>\<phi> x\<^sub>1\<close>] 
              ; (simp only: A B E phi_inheres_in_tranclp)?)
        subgoal G1 by auto
        subgoal G2 
          apply (simp only: C)
          by blast
        subgoal G3
          apply (simp only: phi_tgt_iof_iff ; intro allI impI)
          subgoal premises P for w u
            using P(5) apply (elim exE conjE)
            subgoal premises Q for x\<^sub>3 w\<^sub>1
              apply (intro P(4)[rule_format,of w\<^sub>1 u])
              using Q(3) Q(3)[THEN iof_scope(1)] P(3) inherence_scope[OF P(3)] 
                    phi.morph_is_injective[THEN inj_onD,simplified,OF Q(1)] 
              by metis
            done
          done
        done
      subgoal for x\<^sub>1 x\<^sub>2
        apply (rule inst2.detailingMoments.intros(2)[of _ _ \<open>\<phi> x\<^sub>2\<close>] 
              ; (simp only: A B E phi_inheres_in_tranclp)?)
        by blast
      done
    done
  done
qed      

end

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_inheres_in_scope: 
  assumes \<open>trim_inheres_in U x y\<close>
  shows \<open>x \<in> \<M> - \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<in> \<P> - \<Delta>\<^bsub>U\<^esub>\<close>  
  subgoal 
    using assms by (meson DiffI \<M>_I trim_inheres_in_D(1) trim_inheres_in_D(2))
  using assms apply (elim trim_inheres_in_E)
  by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_towards_scope: 
  assumes \<open>trim_towards U x y\<close>
  shows \<open>x \<in> \<M> - \<Delta>\<^bsub>U\<^esub>\<close> \<open>y \<in> \<P> - \<Delta>\<^bsub>U\<^esub>\<close>  
  subgoal using assms using trim_towards_def by auto
  using assms trim_towards_E by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_assoc_quale_scope_E: 
  assumes \<open>trim_assoc_quale U x q\<close>
  obtains \<open>x \<in> \<M> - \<Delta>\<^bsub>U\<^esub>\<close> \<open>q \<in> quality_space_sig.qualia (trim_quality_spaces U)\<close>  
  using assms apply (elim trim_assoc_quale_E)
  apply (auto simp: quality_space_sig.qualia_def)
  subgoal premises P
    apply (rule P(1))
    subgoal using P(2,3) using assoc_quale_scopeD(3) by blast
    subgoal premises Q 
      using assoc_quale_scopeD(2)[OF Q P(2)] apply (elim \<Q>_E)
      subgoal for A
        apply (rule bexI[of _ A] ; simp?)
        apply (rule trim_quality_spaces_I[of A q U x] ; simp?)
        by (intro trim_assoc_quale_I P Q)
      done
    done
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_assoc_quale_scope_E_1: 
  assumes \<open>trim_assoc_quale U x q\<close>
  obtains 
    \<open>x \<in> \<M> - \<Delta>\<^bsub>U\<^esub>\<close> 
    \<open>q \<in> quality_space_sig.qualia (ps_quality_spaces (trim U))\<close>  
  using assms trim_assoc_quale_scope_E that[simplified trim_simps] by metis

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_substantials[simp]:
   \<open>inherence_sig.\<S> (ps_worlds (trim U)) (ps_inheres_in (trim U))  = \<S>\<close>
  apply (auto simp: inherence_sig.\<S>_def)
  subgoal premises P for x
    using P(3,1,2)
    apply (induct x rule: detailingMoments.induct)
    subgoal using inherence_scope by blast    
    using trans_inheres_in_scope by blast
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_substantials_1[simp]:
   \<open>inherence_sig.\<S> (trim_worlds U) (trim_inheres_in U) = \<S>\<close>
  using trim_substantials[simplified trim_simps] .

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_inheres_in_trancl[simp]:
  \<open>(trim_inheres_in U)\<^sup>+\<^sup>+ x y \<longleftrightarrow> (\<triangleleft>)\<^sup>+\<^sup>+ x y \<and> x \<notin> \<Delta>\<^bsub>U\<^esub> \<and> y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  apply (intro iffI conjI ; (elim conjE)?)
  subgoal G1
    apply (induct rule: tranclp.induct)
    subgoal G1_1 by (simp add: tranclp.r_into_trancl trim_inheres_in_D(1))
    subgoal G1_2 premises P for a b c
      using P(3) apply (elim trim_inheres_in_E)
      subgoal premises Q
        using P(2) Q(1) tranclp.intros(2) by metis
      done
    done
  subgoal G2
    by (induct rule: tranclp.induct ; elim trim_inheres_in_E ; simp)
  subgoal G3
    by (induct rule: tranclp.induct ; elim trim_inheres_in_E ; simp)
  subgoal premises P
    using P apply (induct rule: tranclp.induct)
    subgoal premises Q for a b
      using trim_inheres_in_I[OF Q, THEN tranclp.intros(1)[of \<open>trim_inheres_in U\<close>]].
    subgoal premises Q for a b c
      using Q 
      by (metis (full_types) detailingMoments.simps 
            trim_inheres_in_I tranclp.r_into_trancl tranclp_trans)
    done
  done

context
  fixes U :: 'u
begin

interpretation trim: possible_worlds \<open>trim_worlds U\<close>
  apply (unfold_locales ; simp? ; (elim conjE)?)
  subgoal using injection_to_ZF_exist by blast
  subgoal using at_least_one_possible_world trim_worlds_I by fastforce
  subgoal 
    by (meson Diff_iff instantiation_sig.trim_worlds_I
              particulars_do_not_exist_in_some_world)
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_ed[simp]: \<open>trim.ed x y \<longleftrightarrow> ed x y \<and> x \<notin> \<Delta>\<^bsub>U\<^esub> \<and> y \<notin> \<Delta>\<^bsub>U\<^esub>\<close>
  apply (intro iffI conjI ; elim trim.edE conjE edE ; (intro edI trim.edI)?
            ; simp? ; (elim conjE)? ; simp?)
  subgoal premises P for w
    using P(1)[OF trim_worlds_I,OF P(2), of \<open>w - \<Delta>\<^bsub>U\<^esub>\<close>,simplified,
                simplified P,simplified] .
  subgoal premises P for w
    using P(6) apply (elim trim_worlds_E)
    subgoal premises Q for w\<^sub>1
      supply R1 = P(7)[simplified Q(2),simplified,THEN conjunct1]
      supply R2 = P(5)[OF Q(1)]
      by (simp add: Q(2) R2[OF R1] P(2))
    done
  done

interpretation trim: inherence_base \<open>trim_worlds U\<close> \<open>trim_inheres_in U\<close>
  apply (unfold_locales ; (intro conjI)? ; simp?
          ; (intro conjI)? ; (elim trim_inheres_in_E)? ; simp?)
  subgoal by blast
  subgoal by blast
  subgoal by (simp add: inherence_imp_ed)
  subgoal by (simp add: moment_non_migration)
  done

interpretation trim: inherence \<open>trim_worlds U\<close> \<open>trim_inheres_in U\<close>
  apply (unfold_locales)
  subgoal
    apply (rule wf_subset[to_pred,OF inherence_is_noetherian] ; simp)
    by (auto elim: trim_inheres_in_E)
  subgoal
    apply (rule wf_subset[to_pred,OF inherence_is_wf])
    by (auto elim: trim_inheres_in_E)
  done

interpretation trim: quality_space \<open>trim_quality_spaces U\<close>
  apply (unfold_locales ; (intro notI)? 
        ; (elim trim_quality_spaces_E trim_assoc_quale_E)? 
        ; simp?)  
  using quality_spaces_are_disjoint by auto

interpretation trim: 
    qualified_particulars 
        \<open>trim_worlds U\<close> 
        \<open>trim_inheres_in U\<close> 
        \<open>trim_quality_spaces U\<close>
        \<open>trim_assoc_quale U\<close>
  apply (unfold_locales ; simp? ; (elim conjE)?)
  subgoal G1 for x q
    apply (elim trim_assoc_quale_E ; intro conjI)
    subgoal using assoc_quale_scopeD(3) by blast
    subgoal by blast
    subgoal by (metis instantiation_sig.trim_assoc_quale_def trim_assoc_quale_scope_E)
    done
  subgoal G2 for x q\<^sub>1 q\<^sub>2
    apply (elim trim_assoc_quale_E)    
    by (simp add: assoc_quale_unique)
  subgoal G3 for w y\<^sub>1 y\<^sub>2 x q\<^sub>1 q\<^sub>2 Q
    apply (elim trim_assoc_quale_E trim_inheres_in_E trim_worlds_E
                trim_quality_spaces_E 
          ; simp)    
    by (simp add: quality_moment_unique_by_quality_space)
  subgoal G4 for Q
    by (elim trim_quality_spaces_E ; blast)
  subgoal G5 for y\<^sub>1 x y\<^sub>2 q
    apply (elim trim_assoc_quale_E trim_inheres_in_E ; simp)    
    by (simp add: quale_determines_moment)
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_ultimate_bearer[simp]:
  assumes \<open>x \<in> trim.\<P>\<close>
  shows \<open>trim.ultimateBearer x = !\<beta> x\<close>  
proof -
  have A: \<open>x \<in> \<S> \<Longrightarrow> x \<notin> \<M>\<close> using assms by blast
  show ?thesis
    apply (rule trim.ultimate_bearer_eq_simp[THEN iffD2] ; simp)
    using assms apply (cases x rule: trim.endurant_cases)
    subgoal substantials
      apply simp
      subgoal premises P 
        using assms by force        
      done
    subgoal premises P
      using trim.ultimate_bearer_ex1I[OF P] apply (simp)
      apply (elim ex1E conjE ; simp)
      by (meson endurantI1 trans_inheres_in_scope)
    subgoal premises P
      apply (intro conjI)
      subgoal G1 
        using assms by auto        
      subgoal G2        
        by (smt (z3) assms endurantI3 inherence_sig.\<S>_I
              iso_universals.trim_substantials_1 iso_universals_axioms
              noetherian_inherence.ultimate_bearer_eqI1
              noetherian_inherence.ultimate_bearer_eq_simp
              noetherian_inherence_axioms rtranclp.rtrancl_refl 
              trim.endurantI3 trim.noetherian_inherence_axioms
              trim.ultimate_bearer_ex1I trim_inheres_in_trancl)      
      done
    done
qed


interpretation trim: 
    towardness 
      \<open>trim_worlds U\<close> 
      \<open>trim_inheres_in U\<close> 
      \<open>trim_towards U\<close>
  apply (unfold_locales)
  subgoal for x y
    apply (elim trim_towards_E ;  simp)
    using towardness_scope by simp
  subgoal for x y
    apply (elim trim_towards_E ;  simp)
    using towardness_imp_ed by simp
  subgoal for x y
    apply (elim trim_towards_E)
    subgoal premises P
      supply R1 = towardness_scopeD[OF P(1)]
      supply R2 = 
          trim_ultimate_bearer[
              of x, simplified P(1) trim_particulars_1,OF DiffI, OF R1(2) P(2)]
      using  P R1 R2
      apply (simp only: R2)
      by blast
    done
  subgoal for x y\<^sub>1 y\<^sub>2
    apply (elim trim_towards_E)    
    by (simp add: towardness_single)
  done

interpretation trim: 
  ufo_particular_theory 
    \<open>trim_worlds U\<close> 
    \<open>trim_inheres_in U\<close> 
    \<open>trim_quality_spaces U\<close> 
    \<open>trim_assoc_quale U\<close> 
    \<open>trim_towards U\<close>
  apply (unfold_locales)
  apply (elim trim.qualifiedParticularsE trim_assoc_quale_E ; intro notI
          ; elim trim_inheres_in_E)  
  using qualified_particulars_are_not_bearers by blast

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The trimmed particular structure is also a particular structure:
\<close>
text_raw \<open>\par\<close>
lemma trim_particular_struct[intro!,simp]: 
  \<open>particular_struct (trim U)\<close>
  apply (simp only: particular_struct_def trim_simps)
  by intro_locales

interpretation trim_morph: pre_particular_struct_morphism \<open>trim U\<close> \<Gamma> id
  apply (simp only: pre_particular_struct_morphism_def ; intro conjI)
  subgoal by simp
  subgoal by blast
  apply (unfold_locales ; simp add: trim_simps)
  subgoal by (simp add: trim_quality_spaces_def)
  subgoal by (simp add: trim_inheres_in_def)
  subgoal for x z
    apply auto
    by (metis instantiation_sig.detailingMoments.simps tranclp.r_into_trancl)    
  subgoal by (simp add: trim_towards_def)
  subgoal for x z
    apply auto    
    using trim.endurantI3 by auto    
  by (simp add: trim_assoc_quale_def)


interpretation trim_morph: particular_struct_morphism \<open>trim U\<close> \<Gamma> id
  apply (unfold_locales ; simp add: trim_simps)
  subgoal
    apply (elim trim_worlds_E ; hypsubst_thin)
    subgoal for w
      apply (intro exI[of _ \<open>w\<close>])
      apply (intro trim_morph.world_corresp_I[simplified] 
            ; (simp add: trim_simps)?)
      by (intro trim_worlds_I[of  w] ; simp)
    done
  subgoal for w\<^sub>t
    apply (intro exI[of _ \<open>w\<^sub>t - \<Delta>\<^bsub>U\<^esub>\<close>] trim_morph.world_corresp_I[simplified]
           ; (simp add: trim_simps)? )
    by (intro trim_worlds_I[of  w\<^sub>t] ; simp)
  done

text \<^marker>\<open>tag bodyonly\<close> \<open>
  There is at least one injective morphism from \<open>\<Gamma>\<close> trimmed by \<open>U\<close> (\<open>trim U\<close>) to \<open>\<Gamma>\<close>,
  i.e. the trimmed structure can be considered a sub-structure of \<open>\<Gamma>\<close>:
\<close>
text_raw \<open>\par\<close>
lemma trim_injective[intro!,simp]: 
  \<open>particular_struct_injection (trim U) \<Gamma> id\<close>
  by (unfold_locales ; intro inj_on_id)


lemma  \<^marker>\<open>tag (proof) aponly\<close> trim_worlds_img: 
    \<open>\<exists>w\<^sub>1 \<in> \<W>. w = w\<^sub>1 - \<Delta>\<^bsub>U\<^esub>\<close> if \<open>w \<in> trim_morph.src.\<W>\<close>
  using that apply (simp add: trim_simps)
  by (elim trim_worlds_E ; blast)      

end

lemma  \<^marker>\<open>tag (proof) aponly\<close> detailingMoments_mono[intro]:
  assumes \<open>U\<^sub>1 \<sqsubseteq> U\<^sub>2\<close> 
  shows \<open>\<Delta>\<^bsub>U\<^sub>1\<^esub> \<subseteq> \<Delta>\<^bsub>U\<^sub>2\<^esub>\<close>
proof -
  have A: \<open>x \<in> Insts U\<^sub>2\<close> if  \<open>x \<in> Insts U\<^sub>1\<close> for x
    using that assms subsumesE InstsI InstsE by metis
  have B: \<open>x \<Colon>\<^bsub>w\<^esub> U\<^sub>2\<close> if  \<open>x \<Colon>\<^bsub>w\<^esub> U\<^sub>1\<close> for x w
    using that assms subsumesE  by metis
  have C: \<open>U\<^sub>2 \<in> \<U>\<^sub>\<S>\<close> if \<open>U\<^sub>1 \<in> \<U>\<^sub>\<S>\<close>
  proof -
    obtain x w where \<open>x \<Colon>\<^bsub>w\<^esub> U\<^sub>2\<close> \<open>x \<in> \<S>\<close>
      using assms
      by (meson B \<U>\<^sub>\<S>_E \<open>U\<^sub>1 \<in> \<U>\<^sub>\<S>\<close>)
    then show ?thesis using \<U>\<^sub>\<S>_I by blast
  qed 
  obtain D: \<open>U\<^sub>1 \<in> \<U>\<close> \<open>U\<^sub>2 \<in> \<U>\<close>
    using assms by blast
  show ?thesis
    apply (intro subsetI)
    subgoal for u\<^sub>1
      apply (induct rule: detailingMoments.induct)
      subgoal premises P for x y
        apply (intro detailingMoments.intros(1)[of U\<^sub>2 x y] P A C allI impI notI
              ; elim char_by_E)
        subgoal premises Q for w u
          apply (rule P(4)[rule_format,THEN notE,of w u]
                ; (intro Q char_by_I D)?)
          using B by blast
        done
      subgoal premises P for x y
        by (intro detailingMoments.intros(2)[of x U\<^sub>2 y] P)
      done
    done
qed


end

end
