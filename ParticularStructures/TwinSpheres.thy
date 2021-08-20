text_raw \<open>\section[Twin Spheres  Examples]{Twin Spheres  Examples\isalabel{sec:examples}}\<close>

theory TwinSpheres
  imports SingleWorldStructure
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
The examples of particulars structures presented in this section are 
(loosely) based on the twin spheres case describe in \cite{black45}.
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
First we specify a domain of quales with three values:
\<close>

datatype quale = 
    Q_Dist200M 
  | Q_Radius10M 
  | Q_Radius20M

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The values correspond to:
  \begin{itemize}
  \item @{term \<open>Q_Dist200M\<close>}: is a distance quale corresponding to 200 meters; 
  \item @{term \<open>Q_Radius10M\<close>}: is a radius length quale corresponding to 10 meters;
  \item @{term \<open>Q_Radius20M\<close>}: is a radius length quale corresponding to 20 meters.
  \end{itemize}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Next, we specify a domain of endurants:
\<close>

datatype endurant = 
      Sphere1 
    | Sphere2 
    | Sphere1Radius10M 
    | Sphere2Radius20M 
    | Sphere1Dist200M 
    | Sphere2Dist200M
    | Undefined
    

axiomatization
  where endurantUndefined[simp]: 
          \<open>undefined = Undefined\<close>
      

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The endurants are:
  \begin{itemize}
  \item @{term \<open>Sphere1\<close>}: the first sphere;
  \item @{term \<open>Sphere2\<close>}: the second sphere;
  \item @{term \<open>Sphere1Radius10M\<close>}: a moment representing the first sphere having a 10 meter radius;
  \item @{term \<open>Sphere2Radius20M\<close>}: a moment representing the second sphere having a 20 meter radius;
  \item @{term \<open>Sphere1Dist200M\<close>}: a moment representing the first sphere being 200 meters from the second sphere;
  \item @{term \<open>Sphere2Dist200M\<close>}: a moment representing the second sphere being 200 meters from the first sphere.
  \end{itemize}

We specify our set of possible worlds using the following function,
to construct configurations where there are only two possible worlds, one of which is the empty world and the other having all
the endurants:
\<close>

definition tw_worlds :: 
    \<open>endurant set \<Rightarrow> endurant set set\<close> 
  where
    \<open>tw_worlds X = {\<emptyset>,X}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The next function creates an inherence relation predicate
  from a base set of endurants. It associates the
  first sphere (@{term \<open>Sphere1\<close>}) to the moments 
  @{term \<open>Sphere1Radius10M\<close>} and @{term \<open>Sphere1Dist200M\<close>}
  and the second sphere (@{term \<open>Sphere2\<close>}) to the moments 
  @{term \<open>Sphere2Radius20M\<close>} and @{term \<open>Sphere2Dist200M\<close>}. The
  associations can be restricted by the function's \<open>X\<close> parameter:
  associations are only made between endurants that are in \<open>X\<close>.
\<close>

definition tw_inheres_in :: 
    \<open>endurant set \<Rightarrow> endurant \<Rightarrow> endurant \<Rightarrow> bool\<close> 
  where
    \<open>tw_inheres_in X y x \<longleftrightarrow>
       x \<in> X \<and> y \<in> X \<and>
       (x = Sphere1 \<and> (y = Sphere1Radius10M \<or> y = Sphere1Dist200M) \<or>
        x = Sphere2 \<and> (y = Sphere2Radius20M \<or> y = Sphere2Dist200M))\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> tw_inheres_in_rtrancl_simp:
  \<open>(tw_inheres_in X)\<^sup>*\<^sup>* x y \<longleftrightarrow> x = y \<or> tw_inheres_in X x y\<close>
  apply (intro iffI conjI ; (elim conjE)?)  
  subgoal G1
    apply (cases \<open>x = y\<close>)
    subgoal x_eq_y by simp
    subgoal x_neq_y premises P
      using rtranclpD[of \<open>tw_inheres_in X\<close> x y,OF P(1),simplified P(2),simplified]
      apply (simp add: P(2))      
      by (induct rule: tranclp_induct ; (simp add: tw_inheres_in_def)?
          ; safe)
    done
  by blast
  


text \<^marker>\<open>tag bodyonly\<close> \<open>
  This function creates a quale association predicate
  from a base set of endurants. It associates the quales
  @{term \<open>Q_Radius10M\<close>} and @{term \<open>Q_Radius20M\<close>} to the moments 
  @{term \<open>Sphere1Radius10M\<close>} and @{term \<open>Sphere2Radius20M\<close>},
  respectively, and the quale @{term \<open>Q_Dist200M\<close> } to the
  moments @{term \<open>Sphere1Dist200M\<close>} and @{term \<open>Sphere2Dist200M\<close>}. The  associations can be restricted by the function's \<open>X\<close> parameter:   associations are only made between endurants that are in \<open>X\<close>.
\<close>
definition tw_assoc_quale ::
    \<open>endurant set \<Rightarrow> endurant \<Rightarrow> quale \<Rightarrow> bool\<close> 
  where
    \<open>tw_assoc_quale X x q \<longleftrightarrow> x \<in> X \<and> 
        (x = Sphere1Radius10M \<and> q = Q_Radius10M \<or>
         x = Sphere1Dist200M \<and> q = Q_Dist200M \<or>
         x = Sphere2Radius20M \<and> q = Q_Radius20M \<or> 
         x = Sphere2Dist200M \<and> q = Q_Dist200M) \<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This function creates a towardness predicate
  from a base set of endurants. It associates the substantials
  @{term \<open>Sphere2\<close>} and @{term \<open>Sphere1\<close>} to the moments 
  @{term \<open>Sphere1Dist200M\<close>} and @{term \<open>Sphere2Dist200M\<close>},
  respectively. The  associations can be restricted by the function's \<open>X\<close> parameter:   associations are only made between endurants that are in \<open>X\<close>.
\<close>

definition tw_towards :: 
  \<open>endurant set \<Rightarrow> endurant \<Rightarrow> endurant \<Rightarrow> bool\<close> 
    where
  \<open>tw_towards X x y \<longleftrightarrow>
     x \<in> X \<and> y \<in> X \<and>
     (x = Sphere1Dist200M \<and> y = Sphere2 \<or>
      x = Sphere2Dist200M \<and> y = Sphere1)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 The following is the definition of the
 maximal set of quality spaces that shall
 be used in the examples:
\<close>

definition tw_all_quality_spaces :: 
  \<open>quale set set\<close> 
    where
  \<open>tw_all_quality_spaces \<equiv> 
    { { Q_Dist200M}, 
      {Q_Radius10M,Q_Radius20M} }\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The actual set of quality spaces used in
 each example is given by the following function,
 which restricts @{term \<open>tw_all_quality_spaces\<close>}
 to include only the quales that are associated with
 a moment that is present in the configuration 
 (given by the parameter \<open>X\<close>):
\<close>

definition tw_quality_spaces :: 
  \<open>endurant set \<Rightarrow> quale set set\<close> 
    where
  \<open>tw_quality_spaces X = 
     { Q | Q x q . Q \<in> tw_all_quality_spaces \<and>
                   tw_assoc_quale X x q \<and> q \<in> Q}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The configuration of each example is constructed
  by the following function, which has a single 
  parameter, \<open>X\<close>, that specifies the set of
  endurants present in the configuration:
\<close>

definition tw_part_structure :: 
  \<open>endurant set \<Rightarrow> (endurant,quale) particular_struct\<close> 
    where
  \<open>tw_part_structure X \<equiv> \<lparr>
      ps_quality_spaces = tw_quality_spaces X,
      ps_worlds = tw_worlds X,
      ps_inheres_in = tw_inheres_in X,
      ps_assoc_quale = tw_assoc_quale X,
      ps_towards = tw_towards X \<rparr>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This is the set of endurants in the domain:
\<close>

definition \<open>all_endurants \<equiv> 
       {Sphere1,Sphere1Radius10M,Sphere1Dist200M,
        Sphere2,Sphere2Radius20M,Sphere2Dist200M}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This is the set that includes only the substantials:
\<close>

definition 
  \<open>just_the_substantials \<equiv> {Sphere1,Sphere2}\<close>

text_raw \<^marker>\<open>tag bodyonly\<close> \<open>

  The first configuration is a particular structure that
  includes all endurants, including all the moments with
  their associations: 

\<close>

definition \<open>conf1 \<equiv> tw_part_structure all_endurants\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The second configuration is similar to the first,
  but excludes the moments that represent the radii
  of the spheres:
\<close>

definition \<open>conf2 \<equiv> 
    tw_part_structure (
      all_endurants - {Sphere1Radius10M, Sphere2Radius20M}
    )\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The last configuration only includes the substantials,
  excluding all moments:
\<close>

definition \<open>conf3 \<equiv> 
    tw_part_structure just_the_substantials
  \<close>

lemmas all_defs = 
  conf1_def conf2_def conf3_def
  tw_part_structure_def
  tw_quality_spaces_def
  tw_worlds_def
  tw_inheres_in_def
  tw_assoc_quale_def
  tw_towards_def
  tw_all_quality_spaces_def
  possible_worlds_sig.ed_def
  possible_worlds_sig.\<P>_def
  all_endurants_def
  just_the_substantials_def
  inherence_sig.ultimateBearer_def
  qualified_particulars_sig.qualifiedParticulars_def
(*  particular_struct.simps *)
  possible_worlds_sig.indep_def
  inherence_sig.order_def

lemma \<^marker>\<open>tag (proof) aponly\<close> tw_inheres_in_bounded: \<open>tw_inheres_in X = tw_inheres_in (X \<inter> all_endurants)\<close>
  apply (intro ext)
  by (simp only: tw_inheres_in_def all_endurants_def; auto)

lemma \<^marker>\<open>tag (proof) aponly\<close> tw_inheres_in_scope: \<open>tw_inheres_in X x y \<Longrightarrow> x \<in> all_endurants \<and> y \<in> all_endurants\<close>
  by (simp only: tw_inheres_in_def all_endurants_def; auto)

lemma \<^marker>\<open>tag (proof) aponly\<close> tw_inheres_in_wf[intro!,simp]: \<open>wfP (tw_inheres_in X)\<close>
proof (intro finite_acyclic_wf[to_pred])  
  have \<open>{(y, x). tw_inheres_in X y x} \<subseteq> all_endurants \<times> all_endurants\<close>
    by (auto dest: tw_inheres_in_scope)
  then show \<open>finite {(y, x). tw_inheres_in X y x}\<close>
    apply (rule finite_subset)
    by (simp add: all_endurants_def)
  show \<open>acyclicP (tw_inheres_in X)\<close>
    apply (intro acyclicI[to_pred] allI notI)    
    subgoal for y
      apply (cases y ; simp add: tw_inheres_in_def)      
      subgoal using converse_tranclpE by fastforce
      subgoal using converse_tranclpE by fastforce
      subgoal using tranclp.cases by fastforce 
      subgoal using tranclp.cases by fastforce
      subgoal using tranclp.cases by fastforce
      subgoal using tranclp.cases by fastforce
      subgoal using converse_tranclpE by fastforce
      done
    done
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> tw_inheres_in_noetherian[intro!,simp]: \<open>wfP (tw_inheres_in X)\<inverse>\<inverse>\<close>
proof (intro finite_acyclic_wf[to_pred] ; simp)  
  have \<open>{(y, x). tw_inheres_in X x y} \<subseteq> all_endurants \<times> all_endurants\<close>
    by (auto dest: tw_inheres_in_scope)
  then show \<open>finite {(x, y). tw_inheres_in X y x}\<close>
    apply (rule finite_subset)
    by (simp add: all_endurants_def)
  show \<open>acyclicP (\<lambda>x y. tw_inheres_in X y x)\<close>
    apply (intro acyclicI[to_pred] allI notI)    
    subgoal for y
      apply (cases y ; simp add: tw_inheres_in_def)      
      subgoal using tranclp.cases by fastforce
      subgoal using tranclp.cases by fastforce
      subgoal using converse_tranclpE by fastforce
      subgoal using converse_tranclpE by fastforce
      subgoal using converse_tranclpE by fastforce
      subgoal using converse_tranclpE by fastforce
      subgoal using converse_tranclpE by fastforce
      done
    done
qed        
    
fun \<^marker>\<open>tag aponly\<close> endurant_enum :: \<open>endurant \<Rightarrow> nat\<close> where  
  \<open>endurant_enum Sphere1 = 0\<close> |
  \<open>endurant_enum Sphere2 = 1\<close> |
  \<open>endurant_enum Sphere1Radius10M = 2\<close> |
  \<open>endurant_enum Sphere1Dist200M = 3\<close> |
  \<open>endurant_enum Sphere2Radius20M = 4\<close> |
  \<open>endurant_enum Sphere2Dist200M = 5\<close> |
  \<open>endurant_enum Undefined = 1000\<close>
  

lemma \<^marker>\<open>tag (proof) aponly\<close> endurant_enum_inj: \<open>inj endurant_enum\<close>
  apply (intro inj_onI  ; simp)
  subgoal for x y
    by (cases x ; cases y ; simp)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> endurant_inj_to_zf_ex[intro!,simp]: \<open>\<exists>(f :: endurant \<Rightarrow> ZF). inj f\<close>
proof -
  obtain f :: \<open>nat \<Rightarrow> ZF\<close> where \<open>inj f\<close>    
    using inj_nat2Nat by auto
  then have \<open>inj (f \<circ> endurant_enum)\<close>
    apply (intro comp_inj_on[OF endurant_enum_inj,of f])
    using inj_on_subset by blast
  then show ?thesis by blast
qed

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: particular_struct_defs \<open>conf1\<close> \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close> .

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: possible_worlds \<open>conf1.\<W>\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1 using endurant_inj_to_zf_ex .
  by (auto simp: all_defs)+

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: inherence \<open>conf1.\<W>\<close> \<open>conf1.inheresIn\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  by (auto simp: all_defs)+

lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_moments: \<open>conf1.\<M> = {Sphere1Radius10M,Sphere1Dist200M,
                     Sphere2Radius20M,Sphere2Dist200M}\<close>
  by (auto simp: all_defs inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_substantials: \<open>conf1.\<S> = {Sphere1, Sphere2}\<close>
  by (auto simp: all_defs inherence_sig.\<S>_def conf1_moments inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_qualia: \<open>conf1.qualia = {Q_Radius10M,Q_Radius20M,Q_Dist200M}\<close>
  by (auto simp: all_defs quality_space_sig.qualia_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: qualified_particulars 
      \<open>conf1.\<W>\<close> \<open>conf1.inheresIn\<close> \<open>conf1.\<Q>\<S>\<close> \<open>conf1.assoc_quale\<close>
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  subgoal G1 by (auto simp: all_defs) 
  subgoal G2 by (auto simp: all_defs)
  subgoal G3 
    apply (simp only: conf1_moments conf1_qualia)
    by (auto simp: all_defs)    
  subgoal G4 by (auto simp: all_defs)
  subgoal G5 for w y\<^sub>1 y\<^sub>2 x q\<^sub>1 q\<^sub>2 Q
    (* slow *)
    apply (cases y\<^sub>1 ; simp add: all_defs
           ; cases y\<^sub>2 ; simp add: all_defs
           ; cases x ; simp add: all_defs )  
    by (elim disjE conjE ; simp ; hypsubst_thin)+
  subgoal G6 by (auto simp: all_defs)
  subgoal G7 by (auto simp: all_defs)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_ultimate_bearers[simp]:
  assumes \<open>x \<in> conf1.\<P>\<close>
  shows
  \<open>conf1.ultimateBearer x = 
    (if x = Sphere1Radius10M then Sphere1 else
     if x = Sphere1Dist200M then Sphere1 else
     if x = Sphere2Radius20M then Sphere2 else
     if x = Sphere2Dist200M then Sphere2 else x)\<close>
  
  apply (cases x ; simp ; intro conf1.ultimate_bearer_eq_simp[THEN iffD2] conjI
         ; (simp add: conf1_substantials conf1.endurants_eq_un_moments_subst
                  conf1_moments)?)
  supply A = conf1_def tw_part_structure_def all_endurants_def
            tw_inheres_in_def tw_inheres_in_rtrancl_simp
  subgoal  by (simp add: A)
  subgoal  by (simp add: A)
  subgoal  by (simp add: A)
  subgoal  by (simp add: A)
  subgoal 
    using assms apply simp    
    using conf1.undefined_not_in_particulars by auto
  subgoal 
    using assms apply simp    
    using conf1.undefined_not_in_particulars by auto
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_directed_moments[simp]:
  \<open>conf1.directed_moments = {Sphere1Dist200M,Sphere2Dist200M}\<close>
  by (auto simp: all_defs towardness_sig.directed_moments_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: towardness 
      \<open>conf1.\<W>\<close> \<open>conf1.inheresIn\<close> \<open>conf1.towards\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1 for x y
    (* slow *)
    supply simps = all_defs inherence_sig.\<M>_def inherence_sig.\<S>_def
    by (intro conjI  ; cases x; simp add: simps ; cases y ; simp add: simps) 
  subgoal G2 
    by (simp add: conf1.ed_def ; auto simp: all_defs)
  subgoal G3 premises P for x y 
    apply (rule G2[OF P,THEN conf1.edE])
    subgoal premises Q
      apply (simp only: Q(1,2)[THEN conf1_ultimate_bearers])
      apply (cases x ; simp ; cases y ; simp)
      using P Q by (auto simp: all_defs)
    done
  subgoal G4 by (auto simp: all_defs)
  done

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: ufo_particular_theory
      \<open>conf1.\<W>\<close> \<open>conf1.inheresIn\<close> \<open>conf1.\<Q>\<S>\<close> \<open>conf1.assoc_quale\<close> \<open>conf1.towards\<close> 
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  by (simp add: conf1.qualifiedParticulars_def 
      ; auto simp: all_defs)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The three configurations satisfy the axioms for a
  UFO particular structure:
\<close>

theorem conf1_particular_struct[simp,intro!]: 
    \<open>particular_struct conf1\<close>
  by intro_locales

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf1: particular_struct conf1 \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  by simp

(* ** conf 2 * *)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: particular_struct_defs \<open>conf2\<close> \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close> .

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: possible_worlds \<open>conf2.\<W>\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1 using endurant_inj_to_zf_ex .
  by (auto simp: all_defs) 
  

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: inherence \<open>conf2.\<W>\<close> \<open>conf2.inheresIn\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  by (auto simp: all_defs)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf2_moments: \<open>conf2.\<M> = {Sphere1Dist200M,Sphere2Dist200M}\<close>
  by (auto simp: all_defs inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf2_qualia: \<open>conf2.qualia = {Q_Dist200M}\<close>
  by (auto simp: all_defs quality_space_sig.qualia_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: qualified_particulars 
      \<open>conf2.\<W>\<close> \<open>conf2.inheresIn\<close> \<open>conf2.\<Q>\<S>\<close> \<open>conf2.assoc_quale\<close>
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  subgoal G1 by (auto simp: all_defs) 
  subgoal G2 by (auto simp: all_defs)
  subgoal G3 
    apply (simp only: conf2_moments conf2_qualia)
    by (auto simp: all_defs)    
  subgoal G4 by (auto simp: all_defs)
  subgoal G5 for w y\<^sub>1 y\<^sub>2 x q\<^sub>1 q\<^sub>2 Q
    (* slow *)
    by (cases y\<^sub>1 ; simp add: all_defs
        ; cases y\<^sub>2 ; simp add: all_defs; cases x ; simp add: all_defs)
  subgoal G6 by (auto simp: all_defs)
  subgoal G7 by (auto simp: all_defs)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> conf2_substantials: \<open>conf2.\<S> = {Sphere1, Sphere2}\<close>
  by (auto simp: all_defs inherence_sig.\<S>_def conf2_moments inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf2_ultimate_bearers[simp]:
  assumes \<open>x \<in> conf2.\<P>\<close>
  shows
  \<open>conf2.ultimateBearer x = 
    (if x = Sphere1Dist200M then Sphere1 else
     if x = Sphere2Dist200M then Sphere2 else x)\<close>  
  using assms[simplified conf2_substantials conf2.endurants_eq_un_moments_subst
              conf2_moments]
  by (cases x ; simp ;
        intro conf2.ultimate_bearer_eq_simp[THEN iffD2] ;
        (simp add: conf2_substantials conf2.endurants_eq_un_moments_subst
              conf2_moments )? ;
        intro tranclp_into_rtranclp tranclp.intros(1);
        simp add: conf2_def all_endurants_def tw_part_structure_def tw_inheres_in_def
        )

lemma \<^marker>\<open>tag (proof) aponly\<close> conf2_directed_moments[simp]:
  \<open>conf2.directed_moments = {Sphere1Dist200M,Sphere2Dist200M}\<close>
  by (auto simp: all_defs towardness_sig.directed_moments_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: towardness 
      \<open>conf2.\<W>\<close> \<open>conf2.inheresIn\<close> \<open>conf2.towards\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1 for x y
    (* slow *)
    supply simps = all_defs inherence_sig.\<M>_def inherence_sig.\<S>_def
    by (intro conjI  ; cases x ; simp add: simps ; cases y ; simp add: simps)
  subgoal G2 
    by (simp add: conf2.ed_def ; auto simp: all_defs)
  subgoal G3 premises P for x y 
    apply (rule G2[OF P,THEN conf2.edE])
    subgoal premises Q
      apply (simp only: Q(1,2)[THEN conf2_ultimate_bearers])
      apply (cases x ; simp ; cases y ; simp)
      using P Q by (auto simp: all_defs)
    done
  subgoal G4 by (auto simp: all_defs)  
  done

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: ufo_particular_theory
      \<open>conf2.\<W>\<close> \<open>conf2.inheresIn\<close> \<open>conf2.\<Q>\<S>\<close> \<open>conf2.assoc_quale\<close> \<open>conf2.towards\<close> 
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  by (simp add: conf2.qualifiedParticulars_def 
      ; auto simp: all_defs)

theorem conf2_particular_struct[simp,intro!]: 
    \<open>particular_struct conf2\<close>
  by intro_locales

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf2: particular_struct conf2 \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  by simp

(* conf3 *)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: particular_struct_defs \<open>conf3\<close> \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close> .

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: possible_worlds \<open>conf3.\<W>\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1 using endurant_inj_to_zf_ex .
  by (auto simp: all_defs)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: inherence \<open>conf3.\<W>\<close> \<open>conf3.inheresIn\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  by (auto simp: all_defs)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf3_moments: \<open>conf3.\<M> = \<emptyset>\<close>
  by (auto simp: all_defs inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> conf3_qualia: \<open>conf3.qualia = \<emptyset>\<close>
  by (auto simp: all_defs quality_space_sig.qualia_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: qualified_particulars 
      \<open>conf3.\<W>\<close> \<open>conf3.inheresIn\<close> \<open>conf3.\<Q>\<S>\<close> \<open>conf3.assoc_quale\<close>
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  subgoal G1 by (auto simp: all_defs) 
  subgoal G2 by (auto simp: all_defs)
  subgoal G3 
    apply (simp only: conf3_moments conf3_qualia)
    by (auto simp: all_defs)    
  subgoal G4 by (auto simp: all_defs)
  subgoal G5 for w y\<^sub>1 y\<^sub>2 x q\<^sub>1 q\<^sub>2 Q
    (* slow *)
    apply (cases y\<^sub>1 ; simp add: all_defs ; cases y\<^sub>2 ; simp add: all_defs ; 
           cases x ; simp add: all_defs)
    done
  subgoal G6 by (auto simp: all_defs)
  subgoal G7 by (auto simp: all_defs)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> conf3_ultimate_bearers[simp]:
  assumes \<open>x \<in> conf3.\<P>\<close>
  shows \<open>conf3.ultimateBearer x = x\<close>
  using assms[simplified conf3_def just_the_substantials_def 
              tw_part_structure_def,simplified
              possible_worlds_sig.\<P>_def,
              simplified,
              simplified tw_worlds_def,
              simplified]
  by (rule disjE ; simp ; intro conf3.ultimate_bearer_eq_simp[THEN iffD2]
          ; simp add: conf3_def just_the_substantials_def
            tw_part_structure_def possible_worlds_sig.\<P>_def
            inherence_sig.\<S>_def tw_worlds_def
            inherence_sig.\<M>_def
            tw_inheres_in_def )

lemma \<^marker>\<open>tag (proof) aponly\<close> conf3_directed_moments[simp]:
  \<open>conf3.directed_moments = \<emptyset>\<close>
  by (auto simp: all_defs towardness_sig.directed_moments_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: towardness 
      \<open>conf3.\<W>\<close> \<open>conf3.inheresIn\<close> \<open>conf3.towards\<close> \<open>TYPE(endurant)\<close>
  apply (unfold_locales)
  subgoal G1  
    by (simp only: conf3_moments ; auto simp: all_defs)
  subgoal G2 
    by (simp add: conf3.ed_def ; auto simp: all_defs)
  subgoal G3 premises P for x y 
    apply (rule G2[OF P,THEN conf3.edE])
    subgoal premises Q
      apply (simp only: Q(1,2)[THEN conf3_ultimate_bearers])
      apply (cases x ; simp ; cases y ; simp)
      using P Q by (auto simp: all_defs)
    done
  subgoal G4 by (auto simp: all_defs)
  done
  
interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: ufo_particular_theory
      \<open>conf3.\<W>\<close> \<open>conf3.inheresIn\<close> \<open>conf3.\<Q>\<S>\<close> \<open>conf3.assoc_quale\<close> \<open>conf3.towards\<close> 
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  apply (unfold_locales)
  by (simp add: conf3.qualifiedParticulars_def 
      ; auto simp: all_defs)

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: particular_struct conf3 \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  by intro_locales

theorem conf3_particular_struct[simp,intro!]: 
  \<open>particular_struct conf3\<close>
  by intro_locales

interpretation \<^marker>\<open>tag (proof) aponly\<close> conf3: particular_struct conf3 \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  by simp

end 
