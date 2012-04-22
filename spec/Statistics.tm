<TeXmacs|1.0.7.10>

<style|generic>

<\body>
  <\doc-data|<doc-title|Statistical Analysis of Difficulty
  Control>|<\doc-author-data|<author-name|Some Guy Who Isn't a Statistician>>
    \;
  </doc-author-data>>
    \;

    \;

    \;
  </doc-data>

  <section|Introduction>

  When implementing a Bitcoin style system, it is necessary to continually
  adjust the difficulty level of the blocks in order to maintain a consistent
  rate of blocks. \ For example, Bitcoin aims to maintain a rate of one block
  every ten minutes. \ In this paper we will investigate the statistics
  analysis needed to optimize the difficulty adjustment. \ First we will look
  at the statistics behind the adjustments of the original Bitcoin protocol,
  and then we will incrementally look at improvements we can make.

  <subsection|Original Bitcoin Protocol>

  The original Bitcoin protocol analyses 2016 blocks (approximately 2 weeks)
  in a group to estimate the network hashing rate and adjust the difficulty
  accordingly.

  The original protocol effectively assumes networking hashing rate is some
  unknown non-negative value <math|\<lambda\>> which is constant during the
  2016 blocks. \ To represent this state of knowledge we use the
  uninformative improper Jeffery's prior

  <\equation*>
    p<around*|(|hash rate = \<lambda\><around*|\||I|\<nobracket\>>|)>=<frac|1|\<lambda\>>.
  </equation*>

  This prior gives a uniform distribution to
  <math|ln<around*|(|\<lambda\>|)>>.

  The target is a known value <math|f\<in\><around*|[|0,1|]>>. \ The actual
  target is a 256-bit integer, but here we use <math|f> to represent the
  fraction of acceptable block hashes, where each hash value is equally
  likely to be found during each trial. Typically the fraction <math|f> is
  small enough that the ``law of rare events'' holds and the generation of
  blocks is well approximated by a Poisson process at a rate of
  <math|\<lambda\>f> (to-do: formalize this claim). The probability of
  <math|k> blocks taking time <math|\<tau\>> to find, given a hash rate of
  <math|\<lambda\>> and hence a block rate of <math|\<lambda\>f>, is a gamma
  distribution.

  <\equation*>
    p<around*|(|period=\<tau\>\|k,\<lambda\>|)>=\<Gamma\><around*|(|\<tau\>;k,\<lambda\>f|)>=<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>f*\<tau\>>|\<Gamma\><around*|(|k|)>>.
  </equation*>

  By Bayes's rule, the probability of the hash rate being <math|\<lambda\>>
  given that we observe <math|k> blocks over a time period <math|\<tau\>>,
  given our improper prior, is the also a gamma distribution.

  <\folded-std>
    <\equation*>
      p<around*|(|hash rate = \<lambda\>\|k,\<tau\>,I|)>=\<Gamma\><around*|(|\<lambda\>;k,\<tau\>f|)>=<frac|<around*|(|\<tau\>f|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-\<tau\>*f\<lambda\>>|\<Gamma\><around*|(|k|)>>.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|p<around*|(|hashrate =
        \<lambda\>\|k,\<tau\>,I|)>>|<cell|=>|<cell|<frac|p<around*|(|peroid =
        \<tau\>\|k,\<lambda\>|)>|p<around*|(|period=\<tau\>\|k,I|)>>p<around*|(|hashrate
        = \<lambda\>\|k,I|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>f*\<tau\>>|\<Gamma\><around*|(|k|)>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>>p<around*|(|period=\<tau\>\|k,\<alpha\>|)>p<around*|(|hashrate
        = \<alpha\>\|I|)>\<mathd\>\<alpha\>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>*f\<tau\>>|\<Gamma\><around*|(|k|)>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|\<alpha\>f*|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<alpha\>f*\<tau\>>|\<Gamma\><around*|(|k|)>><frac|1|\<alpha\>>\<mathd\>\<alpha\>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>f|)><rsup|k>e<rsup|-\<alpha\>f\<tau\>><frac|1|\<alpha\>f\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>*|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>f\<tau\>|)><rsup|k>e<rsup|-\<alpha\>f\<tau\>><frac|1|\<alpha\>f*\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>*f\<tau\>|)><rsup|k-1>e<rsup|-\<alpha\>f\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|\<Gamma\><around*|(|k|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|f\<tau\>|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-\<lambda\>f\<tau\>>|\<Gamma\><around*|(|k|)>>>>>>
      </eqnarray*>
    </proof>
  </folded-std>

  <subsection|Orthodoxy Solution>

  Orthodox statistics would typically proceed something like the following.
  Using the gamma distribution we find that the expected hashing rate (aka
  the mean hashing rate) is

  <\folded-std>
    <\equation*>
      \<Epsilon\><around*|[|\<lambda\>|]>=<frac|k*|\<tau\>f>.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|\<Epsilon\><around*|[|\<lambda\>|]>>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>\<lambda\>p<around*|(|hash
        rate=\<lambda\>\|k,\<tau\>,I|)>>\<mathd\>\<lambda\>>>|<row|<cell|>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>\<lambda\><frac|<around*|(|<frac|\<tau\>|f>|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-<frac|\<tau\>*\<lambda\>|f>>|\<Gamma\><around*|(|k|)>>>\<mathd\>\<lambda\>>>|<row|<cell|>|<cell|=>|<cell|<frac|<big-around|\<int\>|<rsub|0><rsup|\<infty\>><around*|(|<frac|\<tau\>\<lambda\>|f>|)><rsup|k>e<rsup|-<frac|\<tau\>*\<lambda\>|f>>>\<mathd\>\<lambda\>|\<Gamma\><around*|(|k|)>>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<big-around|\<int\>|<rsub|0><rsup|\<infty\>><around*|(|<frac|\<tau\>\<lambda\>|f>|)><rsup|k+1-1>e<rsup|-<frac|\<tau\>*\<lambda\>|f>>>\<mathd\><around*|(|<frac|\<tau\>\<lambda\>|f>|)>|\<tau\>\<Gamma\><around*|(|k|)>>>>|<row|<cell|>|<cell|=>|<cell|<frac|f\<Gamma\><around*|(|k+1|)>|\<tau\>\<Gamma\><around*|(|k|)>>>>|<row|<cell|>|<cell|=>|<cell|<frac|f*k|\<tau\>>>>>>
      </eqnarray*>
    </proof>

    \;
  </folded-std>

  If we adjust the target to a new target <math|f<rprime|'>>, the we would
  expect block rate to be

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|\<Epsilon\><around*|[|\<lambda\>|]>f<rprime|'>=<frac|f<rprime|'>*k|f*\<tau\>>.>>>>
  </eqnarray*>

  In order to get one block every 600s, we should set the new target to be

  <\equation*>
    f<rprime|'>=<frac|f*\<tau\>|k<around*|(|600<with|mode|text|s>|)>>.
  </equation*>

  This is essentially the process that the original Bitcoin client follows on
  the occasions when it adjusts the difficulty; however it only adjusts the
  difficulty once every 2016 blocks, and it only uses the last
  <math|k\<assign\>2016> blocks and measures the time <math|\<tau\>> taken
  for these blocks. (Note: due to the ``time-warp'' bug, the time measured
  <math|\<tau\>> the time taken for 2015 blocks).

  <\equation*>
    f<rprime|'>=f<frac|*\<tau\>|2016<around*|(|600<with|mode|text|s>|)>>=f<frac|\<tau\>|1209600<with|mode|text|s>>.
  </equation*>

  where <with|mode|math|1209600s> is 2 weeks.

  <subsection|Bayesian Solution>

  The Bayesian will notice that the orthodoxy solution is not optimal.
  Because only the expected hashing rate is considered, it essentially
  ignores the possibility that our expected hashing rate is not correct. In
  other words, it ignores all the other possible hashing rates, even we know
  that they too have some probability of being correct.

  The correct approach to this problem, given that we are assuming the
  hashing rate is constant, is to compute the probability of the next <math|l
  >blocks taking time <math|t> if we set the hashing rate to
  <math|f<rprime|'>>, given our observation of <math|k> blocks over a time
  period <math|\<tau\>>.

  <\folded-std>
    <\equation*>
      p<around*|(|period<rprime|'>=t\|l,k,\<tau\>,I|)>=<frac|f<rprime|'><rsup|><around*|(|*t*f<rprime|'>|)><rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Beta\><around*|(|l,k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)><rsup|k+l>>
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|p<around*|(|period<rprime|'>=t\|l,k,\<tau\>,I|)>>|<cell|=>|<cell|<big-around|\<int\>|<rsup|\<infty\>><rsub|0>>p<around*|(|period<rprime|'>=t<around*|\||l,\<lambda\>|\<nobracket\>>|)>p<around*|(|hashrate=\<lambda\>\|k,\<tau\>,I|)>\<mathd\>\<lambda\>>>|<row|<cell|>|<cell|=>|<cell|<big-around|\<int\>|<rsup|\<infty\>><rsub|0>><frac|<around*|(|\<lambda\>f<rprime|'>|)><rsup|l>t<rsup|l-1>e<rsup|-t\<lambda\>f<rprime|'>>|\<Gamma\><around*|(|l|)>><frac|<around*|(|\<tau\>f|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-\<tau\>*f\<lambda\>>|\<Gamma\><around*|(|k|)>>\<mathd\>\<lambda\>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<rprime|'><rsup|l>t<rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k|)>><big-around|\<int\>|<rsup|\<infty\>><rsub|0>><rsup|>\<lambda\><rsup|k+l-1>e<rsup|\<um\>\<lambda\><around*|(|t*f<rprime|'>+\<tau\>f|)>>\<mathd\>\<lambda\>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<rprime|'><rsup|l>t<rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)>><big-around|\<int\>|<rsup|\<infty\>><rsub|0>><rsup|>\<lambda\><rsup|k+l-1>e<rsup|\<um\>\<lambda\><around*|(|t*f<rprime|'>+\<tau\>f|)>>\<mathd\><around*|(|\<lambda\><around*|(|t*f<rprime|'>+\<tau\>f|)>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<rprime|'><rsup|l>t<rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)><rsup|k+l>><big-around|\<int\>|<rsup|\<infty\>><rsub|0>><rsup|><around*|(|\<lambda\><around*|(|t*f<rprime|'>+t*f|)>|)><rsup|k+l-1>e<rsup|\<um\>\<lambda\><around*|(|t*f<rprime|'>+\<tau\>f|)>>\<mathd\><around*|(|\<lambda\><around*|(|t*f<rprime|'>+\<tau\>f|)>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<rprime|'><rsup|l>t<rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)><rsup|k+l>>\<Gamma\><around*|(|k+l|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|f<rprime|'><rsup|><around*|(|*t*f<rprime|'>|)><rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Beta\><around*|(|l,k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)><rsup|k+l>>>>>>
      </eqnarray*>
    </proof>
  </folded-std>

  To optimize the value new target <math|f<rprime|'>> we want to pick one
  that minimizes the expected loss for some loss function. \ A good choice of
  loss function the absolute error:

  <\equation*>
    L<rsub|1><around*|(|t|)>=<around*|\||t-600<with|mode|text|s>|\|>
  </equation*>

  but an easier choice of loss function, is the squared error:

  <\equation*>
    L<rsub|2><around*|(|t|)>=<around*|(|t-600<with|mode|text|s>|)><rsup|2>
  </equation*>

  Arguably the squared error loss function is better for our purposes, since
  it is good enough if the time per block is close to 10 minutes, but is much
  worse if it is far from 10 minutes.

  Minimizing the expected squared error amounts to picking an new target
  <math|f<rprime|'>> such that the expected time for next <math|l> blocks is
  <math|l*600<with|mode|text|s>>. The expected time for the next <math|l>
  blocks given a new target of <math|f<rprime|'>> and given our observations
  of <math|k> blocks over time <math|\<tau\>> at a target <math|f> is

  <\folded-std>
    <\equation*>
      \<Epsilon\><around*|[|t|]>=<frac|f\<tau\>*l|f<rprime|'><around*|(|k-1|)>>.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|\<Epsilon\><around*|[|t|]>>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>p<around*|(|period<rprime|'>=t\|l,k,\<tau\>,I|)>>t\<mathd\>t>>|<row|<cell|>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|f<rprime|'><rsup|><around*|(|*t*f<rprime|'>|)><rsup|l-1><around*|(|\<tau\>f|)><rsup|k>|\<Beta\><around*|(|l,k|)>*<around*|(|t*f<rprime|'>+\<tau\>f|)><rsup|k+l>>t\<mathd\>t>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<tau\>f|)><rsup|k>|\<Beta\><around*|(|l,k|)>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|t*f<rprime|'>*|)><rsup|l>|<around*|(|*t*f<rprime|'>+\<tau\>f|)><rsup|<around*|(|k+l|)>>>\<mathd\>t>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<tau\>f|)><rsup|k>|\<Beta\><around*|(|l,k|)>f<rprime|'><around*|(|\<tau\>f|)><rsup|<around*|(|k+l|)>>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|t*f<rprime|'>|)><rsup|l>|<around*|(|<frac|t*f<rprime|'>*|\<tau\>f>+1|)><rsup|<around*|(|k+l|)>>>\<mathd\><around*|(|t*f*<rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|1|\<Beta\><around*|(|l,k|)>f<rprime|'><around*|(|\<tau\>f|)><rsup|l>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|t*f<rprime|'>|)><rsup|l>|<around*|(|<frac|t*f<rprime|'>|\<tau\>*f>+1|)><rsup|<around*|(|k+l|)>>>\<mathd\><around*|(|t*f<rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|\<Beta\><around*|(|l,k|)>f<rprime|'><around*|(|\<tau\>f|)><rsup|l>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|t*f<rprime|'>|)><rsup|l>|<around*|(|<frac|*t*f<rprime|'>|\<tau\>f>+1|)><rsup|<around*|(|k+l|)>>>\<mathd\><around*|(|<frac|t*f<rprime|'>|\<tau\>f>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|\<Beta\><around*|(|l,k|)>f<rprime|'>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|<frac|t*f<rprime|'>|\<tau\>f<rprime|'>>|)><rsup|l>|<around*|(|<frac|t*f<rprime|'>|\<tau\>f>+1|)><rsup|<around*|(|k+l|)>>>\<mathd\><around*|(|<frac|t*f<rprime|'>*|\<tau\>f>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|\<Beta\><around*|(|l,k|)>f<rprime|'>><big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|<frac|t*f<rprime|'>|\<tau\>f<rprime|'>>|)><rsup|l+1-1>|<around*|(|<frac|t*f<rprime|'>|\<tau\>f>+1|)><rsup|<around*|(|k-1+l+1|)>>>\<mathd\><around*|(|<frac|t*f<rprime|'>*|\<tau\>f>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|\<Beta\><around*|(|l,k|)>f<rprime|'>>*\<Beta\><around*|(|l+1,k-1|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|f<rprime|'>><around*|(|<frac|\<Beta\><around*|(|l+1,k-1|)>|\<Beta\><around*|(|l,k|)>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|f<rprime|'>><around*|(|<frac|\<Gamma\><around*|(|l+1|)>\<Gamma\><around*|(|k-1|)>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k|)>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|f<rprime|'>><around*|(|<frac|l*\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k-1|)>|\<Gamma\><around*|(|l|)>\<Gamma\><around*|(|k-1|)><around*|(|k-1|)>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<tau\>f|f<rprime|'>><around*|(|<frac|l*|k-1>|)>>>>>
      </eqnarray*>

      \;
    </proof>
  </folded-std>

  Setting the expected time for the next <math|l> blocks to be
  <math|l*600<with|mode|text|s>> we get

  <\folded-std>
    <\equation*>
      f<rprime|'>=<frac|f\<tau\>|*<around*|(|k-1|)>600<with|mode|text|s>>*.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|l*600<with|mode|text|s>>|<cell|=>|<cell|<frac|f\<tau\>|f<rprime|'>><around*|(|<frac|l*|k-1>|)>>>|<row|<cell|600<with|mode|text|s>>|<cell|=>|<cell|<frac|f\<tau\>|f<rprime|'><around*|(|k-1|)>>>>|<row|<cell|f<rprime|'>>|<cell|=>|<cell|*<frac|f\<tau\>|<around*|(|k-1|)>600<with|mode|text|s>>>>>>
      </eqnarray*>
    </proof>
  </folded-std>

  Notice that this result is independent of <math|l>.

  If we take <math|k\<assign\>2016> blocks, like the original client does, we
  conclude we should set the new target to

  <\equation*>
    f<rprime|'>=f<frac|\<tau\>|<around*|(|2016-1|)>*600<with|mode|text|s>>=f<frac|\<tau\>|1209000<with|mode|text|s>>
  </equation*>

  if we want the expected time per block to be 600s, or if we want to
  minimize the expected square error of the time per block.

  <subsection|Per Block Difficulty Adjustments>

  In this section, we will consider a modified Bitcoin protocol where
  difficulty adjustments are made after each block. \ We will still assume
  that the networking hash rate remains constant, an assumption that we will
  weaken in the next section.

  As before we will use the improper, non-informative Jeffery's for the proir
  hash rate distribution.

  <\equation*>
    p<around*|(|hash rate = \<lambda\><around*|\||I|\<nobracket\>>|)>=<frac|1|\<lambda\>>.
  </equation*>

  Instead of the target <math|f\<in\><around*|[|0,1|]>> being a known
  constant, it will vary (but still be known) for each block. We denote the
  target for the <math|i>th block by <math|f<rsub|i>\<in\><around*|[|0,1|]>>.

  The probability of the hash rate rate being <math|\<lambda\>> after
  observing <math|n> blocks given that the <math|i<rsup|th>> block takes time
  <math|\<tau\><rsub|i>> is

  <\folded>
    <\equation*>
      <with|mode|math|p<around*|(|hash rate =
      \<lambda\>\|\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>=<frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>\<lambda\><rsup|n-1>e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|n|)>>>
    </equation*>
  <|folded>
    <\proof>
      For <math|n=1> we have that\ 

      <\equation*>
        <with|mode|math|p<around*|(|hash rate =
        \<lambda\>\|\<tau\><rsub|0>,I|)>=f<rsub|0>\<tau\><rsub|0>e<rsup|-\<lambda\>f<rsub|0>\<tau\><rsub|0>>>
      </equation*>

      from the previous section.

      Suppose, by induction, <with|mode|math|p<around*|(|hash rate =
      \<lambda\>\|\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>=<frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>\<lambda\><rsup|n-1>e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|n|)>>>

      <\eqnarray*>
        <tformat|<table|<row|<cell|p<around*|(|hash rate =
        \<lambda\>\|\<tau\><rsub|n>,\<ldots\>,\<tau\><rsub|0>,I|)>>|<cell|=>|<cell|<frac|p<around*|(|\<tau\><rsub|1>\|\<lambda\>,\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>*p<around*|(|\<lambda\>\|\<tau\><rsub|n>,\<ldots\>,\<tau\><rsub|0>,I|)>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>p<around*|(|\<tau\><rsub|1>\|<wide|\<lambda\>|~>,\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>*p<around*|(|<wide|\<lambda\>|~>\|\<tau\><rsub|n>,\<ldots\>,\<tau\><rsub|0>,I|)>\<mathd\><wide|\<lambda\>|~>>>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|<around*|(|\<lambda\>*f<rsub|n>|)>e<rsup|-\<lambda\>f<rsub|n>*\<tau\><rsub|n>>|)>*<around*|(|<frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>\<lambda\><rsup|n-1>e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|
        n|)>>|)>|<big-around|\<int\>|<rsup|\<infty\>><rsub|0><around*|(|<around*|(|<wide|\<lambda\>|~>*f<rsub|n>|)>e<rsup|-<wide|\<lambda\>|~>f<rsub|n>*\<tau\><rsub|n>>|)>*<around*|(|<frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><wide|\<lambda\>|~><rsup|n-1>e<rsup|-<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|n|)>>|)>\<mathd\><wide|\<lambda\>|~>>>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>*e<rsup|-\<lambda\>f<rsub|n>*\<tau\><rsub|n>>|)>*<around*|(|\<lambda\><rsup|n-1>e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|)>|<big-around|\<int\>|<rsup|\<infty\>><rsub|0><around*|(|<wide|\<lambda\>|~>*e<rsup|-<wide|\<lambda\>|~>f<rsub|n>*\<tau\><rsub|n>>|)>*<around*|(|<wide|\<lambda\>|~><rsup|n-1>e<rsup|-<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|)>\<mathd\><wide|\<lambda\>|~>>>>>|<row|<cell|>|<cell|=>|<cell|<frac|\<lambda\><rsup|n>*e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>>|<big-around|\<int\>|<rsup|\<infty\>><rsub|0><wide|\<lambda\>|~><rsup|n>*e<rsup|-<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>>\<mathd\><wide|\<lambda\>|~>>>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>\<lambda\><rsup|n>*e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>>|<big-around|\<int\>|<rsup|\<infty\>><rsub|0><around*|(|<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>|)><rsup|n>*e<rsup|-<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>>\<mathd\><around*|[|<wide|\<lambda\>|~><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>|]>>>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>\<lambda\><rsup|n>*e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n+1>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|n+1|)>>>>>>
      </eqnarray*>
    </proof>
  </folded>

  Now we proceed as before. \ We want to set a new target, <math|f<rprime|'>>
  to control the expected time for the next block, <math|t>. \ Given we set a
  new rate of <math|f<rprime|'>> the expected time for the next block is

  <\folded-std>
    <\equation*>
      p<around*|(|period<rprime|'>=t\|\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>=<frac|n*f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>|<around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>>
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|p<around*|(|period<rprime|'>=t\|\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>,I|)>>|<cell|=>|<cell|>>|<row|<cell|<big-around|\<int\>|<rsup|\<infty\>><rsub|0>>p<around*|(|period<rprime|'>=t<around*|\||\<lambda\>|\<nobracket\>>|)>p<around*|(|hashrate=\<lambda\>\|\<tau\><rsub|n-1>,\<ldots\>\<tau\><rsub|0>,I|)>\<mathd\>\<lambda\>>|<cell|=>|<cell|>>|<row|<cell|<big-around|\<int\>|<rsup|\<infty\>><rsub|0>><around*|(|\<lambda\>f<rprime|'>|)>e<rsup|-t\<lambda\>f<rprime|'>><frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>\<lambda\><rsup|n-1>e<rsup|-\<lambda\><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>|\<Gamma\><around*|(|n|)>>\<mathd\>\<lambda\>>|<cell|=>|<cell|>>|<row|<cell|<frac|f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>|\<Gamma\><around*|(|n|)>><big-around|\<int\>|<rsup|\<infty\>><rsub|0>><rsup|>\<lambda\><rsup|n>e<rsup|\<um\>\<lambda\><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>\<mathd\>\<lambda\>>|<cell|=>|<cell|>>|<row|<cell|<frac|f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>|\<Gamma\><around*|(|n|)><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>><big-around|\<int\>|<rsup|\<infty\>><rsub|0>><rsup|><around*|(|\<lambda\><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>|)><rsup|n>e<rsup|\<um\>\<lambda\><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>>\<mathd\><around*|[|\<lambda\><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)>|]>>|<cell|=>|<cell|>>|<row|<cell|<frac|f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>\<Gamma\><around*|(|n+1|)>|\<Gamma\><around*|(|n|)><around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>>>|<cell|=>|<cell|>>|<row|<cell|<frac|n*f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>|<around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>>>|<cell|>|<cell|>>>>
      </eqnarray*>
    </proof>
  </folded-std>

  As before, in order to pick a value of <math|f<rprime|'>> that minimized
  the expected squared error of <math|t> we pick <math|f<rprime|'>> so that
  the expected value of <math|t> is 600s.

  <\folded-std>
    <\equation*>
      \<Epsilon\><around*|[|t|]>=<frac|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i><rsup|>|f<rprime|'><around*|(|n-1|)>>
      = 600<with|mode|text|s>.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|\<Epsilon\><around*|[|t|]>>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>p<around*|(|period<rprime|'>=t\|\<tau\><rsub|n-1>,\<ldots\>,\<tau\><rsub|0>I|)>>t\<mathd\>t>>|<row|<cell|>|<cell|=>|<cell|<big-around|\<int\>|<rsub|0><rsup|\<infty\>><frac|n*f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n>t|<around*|(|t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>>\<mathd\>t>>>|<row|<cell|>|<cell|=>|<cell|n<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n><big-around|\<int\>|<rsub|0><rsup|\<infty\>><frac|<around*|(|t*f<rprime|'>*|)>|<around*|(|*t*f<rprime|'>+<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|n+1>>\<mathd\>t>>>|<row|<cell|>|<cell|=>|<cell|<frac|n|f<rprime|'><around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>><big-around|\<int\>|<rsub|0><rsup|\<infty\>><frac|<around*|(|t*f<rprime|'>|)>|<around*|(|<frac|t*f<rprime|'>*|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>>+1|)><rsup|n+1>>\<mathd\><around*|(|t*f*<rprime|'>|)>>>>|<row|<cell|>|<cell|=>|<cell|<frac|n<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>|f<rprime|'>><big-around|\<int\>|<rsub|0><rsup|\<infty\>><frac|<around*|(|<frac|t*f<rprime|'>|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>>|)>|<around*|(|<frac|t*f<rprime|'>*|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>>+1|)><rsup|n+1>>\<mathd\><around*|(|<frac|t*f*<rprime|'>|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>>|)>>>>|<row|<cell|
        >|<cell|=>|<cell|<around*|(|<frac|n<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>|f<rprime|'>>|)><around*|(|<frac|1|<around*|(|n-1|)>n>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|)><rsup|>|f<rprime|'><around*|(|n-1|)>>>>>>
      </eqnarray*>

      \;
    </proof>
  </folded-std>

  <\equation*>
    f<rprime|'>=<frac|<below|\<Sigma\>|i\<less\>n>f<rsub|i>\<tau\><rsub|i>|<around*|(|n-1|)>600s>
  </equation*>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|1.1|1>>
    <associate|auto-3|<tuple|1.2|1>>
    <associate|auto-4|<tuple|1.3|2>>
    <associate|auto-5|<tuple|1.4|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|Original Bitcoin Protocol
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1.5fn>|Orthodoxy Solution
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|Bayesian Solution
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1.5fn>|Per Block Difficulty Adjustments
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>
    </associate>
  </collection>
</auxiliary>