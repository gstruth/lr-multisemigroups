
section \<open>lr-Multisemigroups\<close>

theory LR_Multisemigroup
  imports Main

begin

text \<open>A multimagma is a set equipped with a multioperation. Multioperations are nothing but ternary relations.\<close>

class multimagma = 
  fixes mcomp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" (infixl "\<odot>" 70) 

begin

text \<open>We define left and right units.\<close>

definition "munitl e = ((\<exists>x. x \<in> e \<odot> x) \<and> (\<forall>x y. y \<in> e \<odot> x \<longrightarrow> y = x))"

definition "munitr e = ((\<exists>x. x \<in> x \<odot> e) \<and> (\<forall>x y. y \<in> x \<odot> e \<longrightarrow> y = x))"

abbreviation "munit e \<equiv> (munitl e \<or> munitr e)"

text \<open>We lift the multioperation to powersets\<close>

definition conv :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<odot>\<^sub>l" 70) where
  "X \<odot>\<^sub>l Y = \<Union>{x \<odot> y |x y. x \<in> X \<and> y \<in> Y}"

lemma conv_exp: "X \<odot>\<^sub>l Y = {z. \<exists>x y. z \<in> x \<odot> y \<and> x \<in> X \<and> y \<in> Y}"
  unfolding conv_def by fastforce

lemma conv_distl: "X \<odot>\<^sub>l \<Union>\<Y> = \<Union>{X \<odot>\<^sub>l Y |Y. Y \<in> \<Y>}"
  unfolding conv_def by blast

lemma conv_distr: "\<Union>\<X> \<odot>\<^sub>l Y  = \<Union>{X \<odot>\<^sub>l Y |X. X \<in> \<X>}"
  unfolding conv_def by blast

end

text \<open>A multimagma is unital if every element has a left and a right unit.\<close>

class unital_multimagma_var = multimagma + 
  assumes munitl_ex: "\<forall>x.\<exists>e. munitl e \<and> e \<odot> x \<noteq> {}"
  assumes munitr_ex: "\<forall>x.\<exists>e. munitr e \<and> x \<odot> e \<noteq> {}"

begin

lemma munitl_ex_var: "\<forall>x.\<exists>e. munitl e \<and> x \<in> e \<odot> x"
  by (metis equals0I local.munitl_def local.munitl_ex)

lemma unitl: "\<Union>{e \<odot> x |e. munitl e} = {x}"
  apply safe
  apply (simp add: multimagma.munitl_def)
  apply simp
  by (metis munitl_ex_var)

lemma munitr_ex_var: "\<forall>x.\<exists>e. munitr e \<and> x \<in> x \<odot> e"
  by (metis equals0I local.munitr_def local.munitr_ex)

lemma unitr: "\<Union>{x \<odot> e |e. munitr e} = {x}"
  apply safe
  apply (simp add: multimagma.munitr_def)
  apply simp
  by (metis munitr_ex_var)

text \<open>In a unital multimagma, elements can have several left or right units.\<close>

lemma "\<forall>x.\<exists>!e. munit e \<and> e \<odot> x = {x}"
  nitpick
  oops

lemma "\<forall>x.\<exists>!e. munit e \<and> x \<odot> e = {x}"
  nitpick 
  oops

end

text \<open>Here is an alternative definition.\<close>

class unital_multimagma = multimagma + 
  fixes E :: "'a set"
  assumes El: "\<Union>{e \<odot> x |e. e \<in> E} = {x}"
  and Er: "\<Union>{x \<odot> e |e. e \<in> E} = {x}"
 
begin

lemma E1: "\<forall>e \<in> E. (\<forall>x y. y \<in> e \<odot> x \<longrightarrow> y = x)"
  using local.El by fastforce

lemma E2: "\<forall>e \<in> E. (\<forall>x y. y \<in> x \<odot> e \<longrightarrow> y = x)"
  using local.Er by fastforce

text \<open>Units are "orthogonal" idempotents.\<close>

lemma unit_id: "\<forall>e \<in> E. e \<in> e \<odot> e"
  using E1 local.Er by fastforce

lemma unit_id_eq: "\<forall>e \<in> E. e \<odot> e = {e}"
  by (simp add: E1 equalityI subsetI unit_id)

lemma unit_comp: "e\<^sub>1 \<in> E \<Longrightarrow> e\<^sub>2 \<in> E \<Longrightarrow>  e\<^sub>1 \<odot> e\<^sub>2 \<noteq> {} \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
  using E1 E2 by blast

lemma unit_comp_iff: "e\<^sub>1 \<in> E \<Longrightarrow> e\<^sub>2 \<in> E \<Longrightarrow> ((e\<^sub>1 \<odot> e\<^sub>2 \<noteq> {}) = (e\<^sub>1 = e\<^sub>2))"
  using unit_comp unit_id by auto

lemma El11: "\<forall>x.\<exists>e \<in> E. x \<in> e \<odot> x"
  using local.El by auto

lemma El12: "\<forall>x.\<exists>e \<in> E. e \<odot> x = {x}"
  using E1 El11 by fastforce

lemma Er11: "\<forall>x.\<exists>e \<in> E. x \<in> x \<odot> e"
  using local.Er by auto

lemma Er12: "\<forall>x.\<exists>e \<in> E. x \<odot> e = {x}"
  using Er Er11 by fastforce

lemma "\<forall>e \<in> E.\<exists>x. x \<in> e \<odot> x"
  using unit_id by blast

lemma "\<forall>e \<in> E.\<exists>x. x \<in> x \<odot> e"
  using unit_id by blast

sublocale unital_multimagma_var
  apply unfold_locales
  unfolding munitl_def munitr_def
  using E1 El11 apply fastforce
  using E2 Er11 by fastforce

text \<open>Now we know that the two definitions are equivalent.\<close>

text \<open>The next two lemmas show that the set of units is a left and right unit of composition at powerset level.\<close>

lemma conv_unl: "E \<odot>\<^sub>l X = X"
  unfolding conv_def
  apply safe
  using E1 apply blast
  using El12 by fastforce

lemma conv_unr: "X \<odot>\<^sub>l E = X"
  unfolding conv_def
  apply safe
  using E2 apply blast
  using Er12 by fastforce

end

text \<open>A multisemigroup is an associative multimagma.\<close>

class multisemigroup = multimagma +
  assumes assoc: "\<Union>{x \<odot> v |v. v \<in> y \<odot> z} = \<Union>{v \<odot> z |v. v \<in> x \<odot> y}"

begin

lemma assoc_exp: "(\<exists>v. w \<in> x \<odot> v \<and> v \<in> y \<odot> z) = (\<exists>v. v \<in> x \<odot> y \<and> w \<in> v \<odot> z)" 
proof-
  have "(\<exists>v. w \<in> x \<odot> v \<and> v \<in> y \<odot> z) = (w \<in> \<Union>{x \<odot> v |v. v \<in> y \<odot> z})"
    by blast
  also have "\<dots> = (w \<in> \<Union>{v \<odot> z |v. v \<in> x \<odot> y})"
    using local.assoc by auto
  finally show ?thesis
    by blast
qed

lemma assoc_var: "{x} \<odot>\<^sub>l (y \<odot> z) = (x \<odot> y) \<odot>\<^sub>l {z}"
  unfolding conv_def assoc_exp
  using local.assoc by force

text \<open>Associativity lifts to powersets.\<close>

lemma conv_assoc: "X \<odot>\<^sub>l (Y \<odot>\<^sub>l Z) = (X \<odot>\<^sub>l Y) \<odot>\<^sub>l Z"
  unfolding conv_exp
  apply clarsimp
  using assoc_exp by blast

end

text \<open>A multimonoid is a unital multisemigroup.\<close>

class multimonoid = multisemigroup + unital_multimagma

begin

text \<open>In a multimonoid, left and right units are unique for each element.\<close>

lemma munits_uniquel: "\<forall>x.\<exists>!e. munit e \<and> e \<odot> x = {x}"
  apply safe
  using local.E1 local.El12 local.munitr_ex_var apply blast
  apply (metis insertI1 local.Er11 local.assoc_exp local.unit_comp_iff multimagma.munitl_def)
  apply (metis insertI1 local.assoc_exp multimagma.munitl_def multimagma.munitr_def)
  apply (metis insertI1 local.assoc_exp multimagma.munitl_def multimagma.munitr_def)
  by (metis insertI1 local.El11 local.assoc_exp local.unit_comp multimagma.munitr_def)

lemma munits_uniquer: "\<forall>x.\<exists>!e. munit e \<and> x \<odot> e = {x}"
  apply safe
  using local.E1 local.Er12 local.munitr_ex_var apply blast
  apply (metis insertI1 local.assoc_exp local.munitr_ex_var multimagma.munitl_def multimagma.munitr_def)
  apply (metis insertI1 local.assoc_exp local.munitl_def multimagma.munitr_def)
  apply (metis insertI1 local.assoc_exp local.munitl_def multimagma.munitr_def)
  by (metis insertI1 local.El11 local.assoc_exp local.unit_comp_iff multimagma.munitr_def)

text \<open>In a monoid, there is of course one single unit, and our definition of many units reduces to this one.\<close>

lemma units_unique: "(\<forall>x y. x \<odot> y \<noteq> {}) \<Longrightarrow> \<exists>!e. munit e"
  apply safe
  using local.munitl_ex_var apply blast
  apply (metis local.Er11 local.unit_comp multimagma.munitl_def)
  apply (metis local.Er11 local.munitl_ex_var local.unit_comp multimagma.munitl_def multimagma.munitr_def)
  apply (metis local.Er11 local.munitl_ex_var local.unit_comp multimagma.munitl_def multimagma.munitr_def)
  by (metis local.El11 local.unit_comp multimagma.munitr_def)

lemma "x \<odot> x = {x} \<Longrightarrow> x \<in> E"
  nitpick
  oops

end



text \<open>Next we define lr-multisemigroups with source and target maps.\<close>

class lr_multimagma = multimagma + 
fixes ll :: "'a \<Rightarrow> 'a"
  and rr :: "'a \<Rightarrow> 'a"
  assumes Dlr: "x \<odot> y \<noteq> {} \<Longrightarrow> rr x = ll y"
  and l_absorb [simp]: "ll x \<odot> x = {x}" 
  and r_absorb [simp]: "x \<odot> rr x = {x}"

begin

lemma rl_compat [simp]: "rr (ll x) = ll x"
  by (simp add: local.Dlr)

lemma lr_compat [simp]: "ll (rr x) = rr x"
  by (metis insert_not_empty local.Dlr local.r_absorb)

lemma ll_retract [simp]: "ll (ll x) = ll x"
  by (metis lr_compat rl_compat)

lemma rr_retract [simp]: "rr (rr x) = rr x"
  by (metis lr_compat rl_compat)

lemma lr_fix: "(rr x = x) = (ll x = x)"
  by (metis lr_compat rl_compat)

definition lfix :: "'a set" where
  "lfix = {x. ll x = x}"

definition rfix :: "'a set" where
  "rfix = {x. rr x = x}"

lemma lr_fix_set: "{x. ll x = x} = {x. rr x = x}"
  using lr_fix by simp

lemma lrfix_set: "lfix = rfix"
  by (simp add: lfix_def rfix_def lr_fix_set)

lemma l_idem [simp]: "ll x \<odot> ll x = {ll x}"
  by (metis local.r_absorb rl_compat)

lemma r_idem [simp]:  "rr x \<odot> rr x = {rr x}"
  by (metis local.l_absorb lr_compat)

lemma lr_comm: "rr x \<odot> ll y = ll y \<odot> rr x"
  using local.Dlr by fastforce

lemma l_weak_twisted: "\<Union>{ll u \<odot> x |u. u \<in> x \<odot> y} \<subseteq> x \<odot> ll y"
  apply (clarsimp simp:  Sup_least) 
  by (metis equals0D local.Dlr local.l_absorb local.r_absorb rl_compat)

lemma "\<Union>{ll u \<odot> x |u. u \<in> x \<odot> y} = x \<odot> ll y"
  nitpick
  oops

lemma r_weak_twisted: "\<Union>{x \<odot> rr u |u. u \<in> y \<odot> x} \<subseteq> rr y \<odot> x"
  apply (clarsimp simp: Sup_least)
  by (metis empty_iff local.Dlr local.l_absorb local.r_absorb lr_compat)

lemma "\<Union>{x \<odot> rr u |u. u \<in> y \<odot> x} = rr y \<odot> x"
  nitpick
  oops

lemma l_comm: "ll x \<odot> ll y = ll y \<odot> ll x"
  using local.Dlr by force

lemma r_comm: "rr x \<odot> rr y = rr y \<odot> rr x"
  using local.Dlr by fastforce

lemma l_export: "ll ` (ll x \<odot> y) = ll x \<odot> ll y"
  using local.Dlr by force

lemma r_export: "rr ` (x \<odot> rr y) = rr x \<odot> rr y"
  by (metis image_empty image_insert local.Dlr local.r_absorb lr_compat r_idem)

lemma lr_prop: "(rr x = ll y) = (rr x \<odot> ll y \<noteq> {})"
  by (metis empty_not_insert l_idem local.Dlr lr_compat rl_compat)
  
lemma weak_local_var: "rr x \<odot> ll y = {} \<Longrightarrow> x \<odot> y = {}"
  using local.Dlr lr_prop by blast

lemma "x \<odot> y = {} \<Longrightarrow> rr x \<odot> ll y = {}"
  nitpick
  oops

lemma "(ll x \<odot> ll y \<noteq> {}) = (ll x = ll y)"
  using local.Dlr by fastforce

lemma "(rr x \<odot> rr y \<noteq> {}) = (rr x = rr y)"
  using local.Dlr by fastforce

text \<open>The set of all sources (and targets) are units at powerset level.\<close>

lemma conv_unl: "lfix \<odot>\<^sub>l X = X"
  unfolding conv_def lfix_def
  apply safe 
   apply (metis empty_iff insert_iff local.Dlr local.l_absorb)
  apply simp 
  using ll_retract local.l_absorb by blast

lemma conv_unr: "X \<odot>\<^sub>l rfix = X" 
  unfolding conv_exp rfix_def
  apply safe
   apply (metis empty_iff insert_iff local.Dlr local.r_absorb)
  apply simp
  using local.r_absorb by fastforce

text \<open>We lift source and target maps to the powerset level and prove laws of modal powerset quantales.\<close>

definition LL :: "'a set \<Rightarrow> 'a set" where
  "LL = image ll"

definition RR :: "'a set \<Rightarrow> 'a set" where
  "RR = image rr"

lemma LR_compat [simp]: "LL (RR X) = RR X"
  by (metis LL_def RR_def image_cong image_image lr_compat)

lemma RL_compat [simp]: "RR (LL X) = LL X"
  by (metis LL_def RR_def image_cong image_image rl_compat)

lemma LL_absorp: "LL X \<odot>\<^sub>l X = X"
  unfolding conv_exp LL_def
  apply safe
  using local.Dlr apply fastforce
  by (metis imageI insertI1 local.l_absorb)

lemma RR_absorp: "X \<odot>\<^sub>l RR X = X"
  unfolding conv_exp RR_def
  apply safe
  apply (metis empty_iff local.Dlr local.r_absorb lr_compat singletonD)
  by force

lemma LL_Sup_pres: "LL (\<Union>\<X>) = \<Union>{LL X |X. X \<in> \<X>}"
  unfolding LL_def by blast

lemma RR_Sup_pres: "RR (\<Union>\<X>) = \<Union>{RR X |X. X \<in> \<X>}"
  unfolding RR_def by blast

lemma LR_comm: "LL X \<odot>\<^sub>l RR Y = RR Y \<odot>\<^sub>l LL X"
  unfolding LL_def RR_def conv_exp
  by (metis (no_types, lifting) empty_iff imageE local.Dlr lr_compat rl_compat)

lemma LL_comm: "LL X \<odot>\<^sub>l LL Y = LL Y \<odot>\<^sub>l LL X"
  by (metis LR_comm RL_compat)

lemma LL_comm: "RR X \<odot>\<^sub>l RR Y = RR Y \<odot>\<^sub>l RR X"
  by (metis LR_comm LR_compat)

lemma RR_subid: "LL X \<subseteq> lfix"
  by (simp add: LL_def image_subsetI lfix_def)

lemma RR_subid: "RR X \<subseteq> rfix"
  by (simp add: RR_def image_subsetI rfix_def)

lemma LL_export: "LL (LL X \<odot>\<^sub>l Y) = LL X \<odot>\<^sub>l LL Y"
  unfolding conv_exp LL_def
  apply safe
  apply (metis empty_iff image_eqI local.Dlr local.l_absorb local.r_absorb singletonD singletonI)
  using l_export by fastforce

lemma RR_export: "RR (X \<odot>\<^sub>l RR Y) = RR X \<odot>\<^sub>l RR Y"
  unfolding conv_exp RR_def
  apply safe
  apply (metis empty_iff image_eqI local.Dlr local.r_absorb r_idem singletonD singletonI)
  using r_export by fastforce

end

class lr_multisemigroup = lr_multimagma + multisemigroup

begin

lemma l_comp_aux: "v \<in> x \<odot> y \<Longrightarrow> ll v = ll x"
proof-
  assume hyp: "v \<in> x \<odot> y"
  hence "v \<in> ll v \<odot> v \<and> v \<in> x \<odot> y"
    by simp
  hence "\<exists>w. w \<in> ll v \<odot> x \<and> v \<in> w \<odot> y"
    using local.assoc by blast
  hence "rr (ll v) = ll x"
    using local.Dlr by fastforce
  thus ?thesis
    by simp
qed

lemma l_comp: "LL (x \<odot> y) \<subseteq> {ll x}"
  by (simp add: LL_def image_subsetI l_comp_aux)

lemma l_comp_cond: "x \<odot> y \<noteq> {} \<Longrightarrow> LL (x \<odot> y) = {ll x}"
  by (metis empty_is_image l_comp local.LL_def subset_singleton_iff)
 
lemma r_comp_aux: "v \<in> x \<odot> y \<Longrightarrow> rr v = rr y"
proof-
  assume hyp: "v \<in> x \<odot> y"
  hence "v \<in> v \<odot> rr v \<and> v \<in> x \<odot> y"
    by simp
  hence "\<exists>w. w \<in> y \<odot> rr v \<and> v \<in> x \<odot> w"
    using local.assoc by blast
  hence "ll (rr v) = rr y"
    using local.Dlr by fastforce
  thus ?thesis
    by simp
qed

lemma r_comp: "RR (x \<odot> y) \<subseteq> {rr y}"
  by (simp add: RR_def image_subsetI r_comp_aux)

lemma r_comp_cond: "x \<odot> y \<noteq> {} \<Longrightarrow> RR (x \<odot> y) = {rr y}"
  by (metis empty_is_image local.RR_def r_comp subset_singleton_iff)

lemma l_weak_local:  "LL (x \<odot> y) \<subseteq> LL (x \<odot> ll y)"
  by (metis insert_not_empty l_comp l_comp_cond local.Dlr local.r_absorb order_class.order.eq_iff)

lemma l_local_cond:  "x \<odot> y \<noteq> {} \<Longrightarrow> LL (x \<odot> y) = LL (x \<odot> ll y)"
  by (metis insert_not_empty l_comp_cond local.Dlr local.r_absorb)

lemma r_weak_local:  "RR (x \<odot> y) \<subseteq> RR (rr x \<odot> y)"
  using RR_def local.Dlr r_comp_cond by fastforce

lemma r_local_cond:  "x \<odot> y \<noteq> {} \<Longrightarrow> RR (x \<odot> y) = RR (rr x \<odot> y)"
  using r_comp r_comp_cond r_weak_local by fastforce

lemma r_twisted_aux: "u \<in> x \<odot> y \<Longrightarrow> (rr x \<odot> y = y \<odot> rr u)"
  using local.Dlr r_comp_aux by fastforce

lemma r_twisted_cond: "x \<odot> y \<noteq> {} \<Longrightarrow> rr x \<odot> y = \<Union>{y \<odot> rr u |u. u \<in> x \<odot> y}"
  by (simp add: Setcompr_eq_image local.Dlr r_comp_aux)

lemma l_twisted_aux: "u \<in> x \<odot> y \<Longrightarrow> (x \<odot> ll y = ll u \<odot> x)"
  by (metis l_comp_aux local.Dlr local.l_absorb local.r_absorb)

lemma l_twisted_cond: "x \<odot> y \<noteq> {} \<Longrightarrow> x \<odot> ll y = \<Union>{ll u \<odot> x |u. u \<in> x \<odot> y}"
  apply standard
  using l_twisted_aux apply fastforce
  by (simp add: local.l_weak_twisted)

lemma "x \<in> y \<odot> z \<Longrightarrow> x' \<in> y \<odot> z \<Longrightarrow> ll x = ll x'"
  by (simp add: l_comp_aux)

lemma coherence_iff: "(\<forall>x y. (x \<odot> y \<noteq> {}) = (rr x = ll y)) = (\<forall>v x y z. v \<in> x \<odot> y \<longrightarrow> y \<odot> z \<noteq> {} \<longrightarrow> v \<odot> z \<noteq> {})"
  by (metis (full_types) insert_not_empty local.Dlr local.l_absorb local.r_absorb r_comp_aux singletonI)

lemma "LL (x \<odot> y) = LL (x \<odot> ll y)"
  nitpick
  oops

lemma r_local:  "RR (x \<odot> y) = RR (rr x \<odot> y)"
  nitpick 
  oops

  text \<open>Again we can lift to properties of modal semirings.\<close>

lemma LL_weak_local: "LL (X \<odot>\<^sub>l Y) \<subseteq> LL (X \<odot>\<^sub>l LL Y)"
  unfolding conv_exp LL_def image_def
  using l_comp_aux local.Dlr local.r_absorb by blast

lemma RR_weak_local: "RR (X \<odot>\<^sub>l  Y) \<subseteq> RR (RR X \<odot>\<^sub>l Y)"
  unfolding conv_exp RR_def image_def
  using r_comp_aux r_twisted_aux by fastforce

end

class coherent_lr_multisemigroup = lr_multisemigroup +
  assumes coherence: "(x \<odot> y \<noteq> {}) = (rr x = ll y)"

begin

text \<open>Coherence implies locality.\<close>

lemma l_local:  "LL (x \<odot> y) = LL (x \<odot> ll y)"
  by (metis local.coherence local.l_local_cond local.ll_retract)

lemma r_local:  "RR (x \<odot> y) = RR (rr x \<odot> y)"
  by (metis local.coherence local.r_local_cond local.rr_retract)

lemma r_twisted: "rr x \<odot> y = \<Union>{y \<odot> rr u |u. u \<in> x \<odot> y}"
  by (metis Setcompr_eq_image Union_empty image_empty local.coherence local.r_twisted_cond local.rr_retract)

lemma l_twisted: "x \<odot> ll y = \<Union>{ll u \<odot> x |u. u \<in> x \<odot> y}"
  by (metis Setcompr_eq_image Union_empty image_empty local.coherence local.l_twisted_cond local.ll_retract)

lemma "LL (x \<odot> y) = {ll x}"
  nitpick
  oops

lemma "RR (x \<odot> y) = {rr x}"
  nitpick
  oops

lemma local_var: "x \<odot> y = {} \<Longrightarrow> rr x \<odot> ll y = {}"
  by (metis local.coherence local.ll_retract local.rr_retract)

lemma local_var_eq: "(x \<odot> y = {}) = (rr x \<odot> ll y = {})"
  by (meson local.weak_local_var local_var)

lemma LL_local: "LL (X \<odot>\<^sub>l Y) = LL (X \<odot>\<^sub>l LL Y)"
  apply (rule antisym)
  apply (simp add: local.LL_weak_local)
  unfolding conv_exp LL_def image_def
  using l_twisted local.l_comp_aux by fastforce

lemma RR_local: "RR (X \<odot>\<^sub>l Y) = RR (RR X \<odot>\<^sub>l Y)"
  apply (rule antisym)
  apply (simp add: local.RR_weak_local)
  unfolding conv_exp RR_def image_def
  apply clarsimp
  using local.r_comp_aux r_twisted by fastforce

end

text \<open>Next we define local lr-multimagmas\<close>

class local_lr_multimagma = lr_multimagma +
  assumes l_local: "LL (x \<odot> ll y) \<subseteq> LL (x \<odot> y)"
  and r_local: "LL (rr x \<odot> y) \<subseteq>  LL (x \<odot> y)"

begin

text \<open>Locality implies coherence, which is the composition pattern of categories.\<close>

lemma  coherence: "(x \<odot> y \<noteq> {}) = (rr x = ll y)"
  apply standard
  apply (simp add: local.Dlr)
  by (metis image_empty local.LL_def local.l_export local.l_idem local.lr_prop local.r_local singleton_insert_inj_eq subset_antisym)

end

text \<open>Finally, we try to derive the implication used in the definition of lr-multisemigroups, but can't.\<close>

class st_multimagma = multimagma + 
  fixes \<sigma> :: "'a \<Rightarrow> 'a"
  and \<tau> :: "'a \<Rightarrow> 'a"
  assumes st_compat [simp]: "\<sigma> (\<tau> x) = \<tau> x"
  and ts_compat [simp]: "\<tau> (\<sigma> x) = \<sigma> x"
  and s_absorb [simp]: "\<sigma> x \<odot> x = {x}" 
  and t_absorb [simp]: "x \<odot> \<tau> x = {x}"
  and st_comm: "\<sigma> x \<odot> \<tau> y = \<tau> y \<odot> \<sigma> x"
  and s_weak_local: "\<sigma> ` (x \<odot> y) \<subseteq> \<sigma> ` (x \<odot> \<sigma> y)"
  and t_weak_local: "\<tau> ` (x \<odot> y) \<subseteq> \<sigma> ` (\<tau> x \<odot> y)"
and l_export: "\<sigma> ` (\<sigma> x \<odot> y) = \<sigma> x \<odot> \<sigma> y"
and  r_export: "\<tau> ` (x \<odot> \<tau> y) = \<tau> x \<odot> \<tau> y"
 
begin

lemma "x \<odot> y \<noteq> {} \<Longrightarrow> \<tau> x \<odot> \<sigma> y \<noteq> {}"
  by (metis empty_is_image empty_subsetI local.s_weak_local local.t_weak_local subset_antisym)

lemma "x \<odot> y = {} \<Longrightarrow> \<tau> x \<odot> \<sigma> y = {}"
  nitpick
  oops

lemma "x \<odot> y \<noteq> {} \<Longrightarrow> \<tau> x = \<sigma> y"
  nitpick
  oops

lemma lr_prop: "(\<tau> x = \<sigma> y) \<Longrightarrow> (\<tau> x \<odot> \<sigma> y \<noteq> {})"
  by (metis empty_not_insert local.t_absorb local.ts_compat)

lemma lr_prop: "(\<tau> x = \<sigma> y) = (\<tau> x \<odot> \<sigma> y \<noteq> {})"
  nitpick 
  oops


lemma s_retract [simp]: "\<sigma> (\<sigma> x) = \<sigma> x"
  by (metis local.st_compat local.ts_compat)

lemma t_retract [simp]: "\<tau> (\<tau> x) = \<tau> x"
  by (metis local.st_compat local.ts_compat)

lemma st_fix: "(\<tau> x = x) = (\<sigma> x = x)"
  by (metis local.st_compat local.ts_compat)

lemma s_idem [simp]: "\<sigma> x \<odot> \<sigma> x = {\<sigma> x}"
  by (metis local.s_absorb s_retract)

lemma t_idem [simp]:  "\<tau> x \<odot> \<tau> x = {\<tau> x}"
  by (metis local.t_absorb t_retract)

lemma s_weak_twisted: "\<Union>{\<sigma> u \<odot> x |u. u \<in> x \<odot> y} \<subseteq> x \<odot> \<sigma> y"
  apply (clarsimp simp:  Sup_least) 
  nitpick
  oops

lemma t_weak_twisted: "\<Union>{x \<odot> \<tau> u |u. u \<in> y \<odot> x} \<subseteq> \<tau> y \<odot> x"
  apply (clarsimp simp: Sup_least)
  nitpick
  oops

lemma s_comm: "\<sigma> x \<odot> \<sigma> y = \<sigma> y \<odot> \<sigma> x"
  by (metis local.st_comm local.ts_compat)

lemma t_comm: "\<tau> x \<odot> \<tau> y = \<tau> y \<odot> \<tau> x"
  by (metis local.st_comm local.st_compat)


end

class st_multisemigroup = st_multimagma + multisemigroup

begin

lemma "x \<odot> y = {} \<Longrightarrow> \<tau> x \<odot> \<sigma> y = {}"
  nitpick
  oops

lemma "x \<odot> y \<noteq> {} \<Longrightarrow> \<tau> x = \<sigma> y"
  nitpick
  oops

lemma lr_prop: "(\<tau> x = \<sigma> y) \<Longrightarrow> (\<tau> x \<odot> \<sigma> y \<noteq> {})"
  by (metis empty_not_insert local.t_absorb local.ts_compat)

lemma lr_prop: "(\<tau> x = \<sigma> y) = (\<tau> x \<odot> \<sigma> y \<noteq> {})"
  nitpick 
  oops

end

class local_st_multisemigroup = st_multisemigroup +
  assumes s_local: "\<sigma> ` (x \<odot> \<sigma> y) \<subseteq> \<sigma> ` (x \<odot> y)"
  and t_local: " \<sigma> ` (\<tau> x \<odot> y) \<subseteq> \<tau> ` (x \<odot> y)"

begin

lemma "x \<odot> y = {} \<Longrightarrow> \<tau> x \<odot> \<sigma> y = {}"
  by (metis image_empty local.l_export local.st_compat local.t_local subset_empty)

lemma "(x \<odot> y = {}) = (\<tau> x \<odot> \<sigma> y = {})"
  by (metis empty_is_image local.l_export local.st_compat local.t_local local.t_weak_local subset_antisym)

lemma "\<tau> x \<odot> \<sigma> y \<noteq> {} \<Longrightarrow> \<tau> x = \<sigma> y"
  nitpick
  oops

end

end



