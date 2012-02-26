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
  <math|<frac|\<lambda\>|f>> (to-do: formalize this claim). The probability
  of <math|k> blocks taking time <math|\<tau\>> to find, given a hash rate of
  <math|\<lambda\>> and hence a block rate of <math|\<lambda\>f>, is a gamma
  distribution.

  <\equation*>
    p<around*|(|period=\<tau\>\|k,\<lambda\>|)>=\<gamma\><around*|(|\<tau\>;k;\<lambda\>f|)>=<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>f*\<tau\>>|\<Gamma\><around*|(|k|)>>.
  </equation*>

  By Bayes's rule, the probability of the hash rate being <math|\<lambda\>>
  given that we observe <math|k> blocks over a time period <math|\<tau\>>,
  given our improper prior, is the also a gamma distribution.

  <\folded-std>
    <\equation*>
      p<around*|(|hash rate = \<lambda\>\|k,\<tau\>,I|)>=\<gamma\><around*|(|\<lambda\>;k,\<tau\>f|)>=<frac|<around*|(|\<tau\>f|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-\<tau\>*f\<lambda\>>|\<Gamma\><around*|(|k|)>>.
    </equation*>
  <|folded-std>
    <\proof>
      \;

      <\eqnarray*>
        <tformat|<table|<row|<cell|p<around*|(|hashrate =
        \<lambda\>\|k,\<tau\>,I|)>>|<cell|=>|<cell|<frac|p<around*|(|peroid =
        \<tau\>\|k,\<lambda\>|)>|p<around*|(|period=\<tau\>\|k,I|)>>p<around*|(|hashrate
        = \<lambda\>\|k,I|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>f*\<tau\>>|\<Gamma\><around*|(|k|)>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>>p<around*|(|period=\<tau\>\|k,\<alpha\>|)>p<around*|(|hashrate
        = \<alpha\>\|I|)>\<mathd\>\<alpha\>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<frac|<around*|(|\<lambda\>*f|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<lambda\>*f\<tau\>>|\<Gamma\><around*|(|k|)>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><frac|<around*|(|\<alpha\>f*|)><rsup|k>\<tau\><rsup|k-1>e<rsup|-\<alpha\>f*\<tau\>>|\<Gamma\><around*|(|k|)>><frac|1|\<alpha\>>\<mathd\>\<alpha\>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>f|)><rsup|k>e<rsup|-\<alpha\>f\<tau\>><frac|1|\<alpha\>f\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>*|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>f\<tau\>|)><rsup|k>e<rsup|-\<alpha\>f\<tau\>><frac|1|\<alpha\>f*\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|<big-around|\<int\>|<rsub|0><rsup|\<infty\>>><around*|(|\<alpha\>*f\<tau\>|)><rsup|k-1>e<rsup|-\<alpha\>f\<tau\>>\<mathd\><around*|(|\<alpha\>f\<tau\>|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|\<lambda\>f\<tau\>|)><rsup|k>e<rsup|-\<lambda\>f\<tau\>>|\<Gamma\><around*|(|k|)>><around*|(|<frac|1|\<lambda\>>|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|<around*|(|f\<tau\>|)><rsup|k>\<lambda\><rsup|k-1>e<rsup|-<frac|\<lambda\>\<tau\>|f>>|\<Gamma\><around*|(|k|)>>>>>>
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
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|1.1|1>>
    <associate|auto-3|<tuple|1.2|1>>
    <associate|auto-4|<tuple|1.3|2>>
    <associate|auto-5|<tuple|1|?>>
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
    </associate>
  </collection>
</auxiliary>