<TeXmacs|1.0.7.11>

<style|article>

<\body>
  <doc-data|<doc-title|Working Title>|<doc-subtitle|Traversing through the
  Looking Glass>|<\doc-author-data|<author-name|Edward Kmett>>
    \;
  </doc-author-data>|<\doc-author-data|<author-name|Twan van Laarhoven>>
    \;
  </doc-author-data>|<\doc-author-data|<author-name|Russell
  O'Connor>|<author-email|oconnorr@google.com>>
    \;
  </doc-author-data>>

  <assign|section-nr|-1><section|Licence>

  <section|Introduction>

  <section|Lenses>

  It is a common programming idiom to access a field of a record via getter
  and setter functions. For example, consider the following personel record

  <\verbatim>
    data Person = Person String -- Name

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ String -- Address

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ String -- Email
  </verbatim>

  \;

  We can define getters for each fields

  <\verbatim>
    get_name, get_address, get_email :: Person -\<gtr\> String

    get_name (Person name _ _) = name

    get_address (Person _ address _) = address

    get_email (Person _ _ email) = email
  </verbatim>

  \;

  And we can define the setters for the each field

  <\verbatim>
    set_name, set_address, set_email :: String -\<gtr\> Person -\<gtr\>
    Persion

    set_name name (Person _ address email) = Person name address email

    set_name address (Person name _ email) = Person name address email

    set_name email (Person name address _) = Person name address email
  </verbatim>

  \;

  In function programming all values are immutable, so that the setter
  function returns a new record that is a copy of the orginal record with the
  field updated.

  In general, suppose <verbatim|a> is the type of a record and <verbatim|b>
  is the type of one of its fields. We can formalize this accessor idiom in a
  structure known as a lens, also known as a functional reference.

  <\verbatim>
    data Lens a b = Lens { getter :: a -\<gtr\> b

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ , setter :: b -\<gtr\> a
    -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }
  </verbatim>

  For example, we can build a lens for the <verbatim|name> field of
  <verbatim|Person> as follows.

  <\verbatim>
    name :: Lens Person String

    name = Lens get_name set_name
  </verbatim>

  \;

  In order for the getter and setter to be coherent we require it to satify
  three laws.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<with|mode|text|<verbatim|getter>> l
    <around*|(|<with|mode|text|<verbatim|setter>> l b
    a|)>>|<cell|=>|<cell|b>>|<row|<cell|<with|mode|text|<verbatim|setter>> l
    <around*|(|<with|mode|text|<verbatim|getter>> l a|)>
    a>|<cell|=>|<cell|a>>|<row|<cell|<with|mode|text|<verbatim|setter>> l
    b<rsub|2> <around*|(|<with|mode|text|<verbatim|setter>> l b<rsub|1>
    a|)>>|<cell|=>|<cell|<with|mode|text|<verbatim|setter>> l b<rsub|2> a>>>>
  </eqnarray*>

  The first law says that you get what you set. \ The second law says that if
  you reset the value you get, the resulting record is the same as you
  started with. The third law says that the second setting obliterates the
  first setting. \ These three laws are the laws of Pierce's <em|very-well
  behaved lens>. \ In this paper we will only be considering <em|very-well
  behaved lenses>, and we will simply call them <em|lenses>.
  <with|color|red|Also the laws of Kagawa.>

  We cannot use the type system to enforce these laws, so we will assume that
  anyone who create a value of type <verbatim|Lens a b> has verified that
  these three laws hold. We consider values that do not satify these laws as
  invalid.

  <subsection|Using Lenses>

  Infix functions for getters and setters provide lightweight notation for
  accessing fields of records.

  <\verbatim>
    (^.) :: a -\<gtr\> Lens a b -\<gtr\> b

    a^.l = getter l a

    \;

    (\<less\>~) :: Lens a b -\<gtr\> b -\<gtr\> a -\<gtr\> a

    l \<less\>~ v = setter l v

    \;

    (%~) :: Lens a b -\<gtr\> (b -\<gtr\> b) -\<gtr\> a -\<gtr\> a

    l \<less\>~ f = \\a -\<gtr\> l \<less\>~ f (a^.l) $ a
  </verbatim>

  \;

  For example, suppose have the following <verbatim|Person>.

  <\verbatim>
    harper :: Person

    harper = Person

    \ \ ``Steven Harper''

    \ \ ``Calgary''

    \ \ ``steven@example.com''
  </verbatim>

  \;

  We can access and update this person with our operators.

  \;

  <\eqnarray*>
    <tformat|<table|<row|<cell|<with|mode|text|<verbatim|harper^.name>>>|<cell|=>|<cell|<with|mode|text|<verbatim|``Steven
    Harper''>>>>|<row|<cell|<with|mode|text|<verbatim|address\<less\>~harper
    $ ``Ottawa''>>>|<cell|=>|<cell|<with|mode|text|<verbatim|Person ``Steven
    Harper'' ``Ottawa'' ``steven@example.com''>>>>>>
  </eqnarray*>

  <subsection|Combining Lenses>

  A powerful features of lenses is that they are composable in the sense that
  they form a <verbatim|Category>.

  <\verbatim>
    instance Category Lens where

    \ \ id :: Lens a a

    \ \ id = Lens id (const id)

    \ \ (.) :: Lens b c -\<gtr\> Lens a b -\<gtr\> Lens a c

    \ \ l2 . l1 = Lens (getter l2 . getter l1)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ (\\c -\<gtr\> l1 %~ (l2 \<less\>~ c))
  </verbatim>

  \;

  <with|color|red|Example.>

  <subsection|Lens for Maps>

  Lenses can be used for structures other than records. \ They can be used
  for any structure to refer to a particular substructure, even substructures
  that are not synticitcally substructures by construction, but are only
  semantically substructures. \ Consider the example of
  <verbatim|Data.Map.Map>. For each key, we can build a lens that references
  the location corresponding to that key.

  <\verbatim>
    at :: (Ord k) =\<gtr\> k -\<gtr\> Lens (Map k v) (Maybe v)

    at k = Lens (lookup k) (\\v m -\<gtr\> maybe (delete k m) (\\v' -\<gtr\>
    insert k v m) v)
  </verbatim>

  \;

  Given a map <verbatim|m> \ we can lookup a value at the key <verbatim|k>
  with <verbatim|m^.at k> which will return <verbatim|Nothing> if the key is
  not in the map, and returns <verbatim|Just v> if there is a key in the map.
  The setter is used both delete and insert values into the map. \ The
  expression <verbatim|at k \<less\>~ Nothing $ m> will remove the key from
  the map, and the expression <verbatim|at k \<less\>~ Just v $ m> will
  insert or overwrite the value <verbatim|v> into the map <verbatim|m> at key
  <verbatim|k>.

  Notice that <verbatim|Maybe v> isn't syntatically a substructure of the
  <verbatim|Data.Map> implementation, however it is semantically a
  substructure, so we can build lenses that reference it. The interested
  reader can verify that the three lens laws hold.

  <subsection|Coalgebra of the Store Comonad>

  Both the getter and setter function have a parameter of type <verbatim|a>,
  the type of the record, so we can factor<with|color|red|?> the
  <verbatim|Lens> structure into the type <verbatim|a -\<gtr\> (b, b -\<gtr\>
  a)>. The codomain of this structure, <verbatim|(b, b -\<gtr\> a)> is known
  as a <em|store> comonad, and is dual to the familiar a state monad. \ Thus
  we can alternatively define a lens structure as

  <\verbatim>
    data Store i a = Store { peek :: i -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ ,
    <with|font-series|bold|pos :: i>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }

    \;

    newtype Lens a b = Lens { runLens :: a -\<gtr\> Store b a }
  </verbatim>

  \;

  We can build our example lens for the <verbatim|name> field of
  <verbatim|Person> as follows.

  <\verbatim>
    nameLens :: Lens Person String

    nameLens = Lens \\(Person name address email) -\<gtr\>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ Store (\\newName -\<gtr\> Person newName
    address email) name
  </verbatim>

  \;

  With this representation, the getter and setter functions are defined as
  follows.

  \;

  <\verbatim>
    getter :: Lens a b -\<gtr\> a -\<gtr\> b

    getter l a = pos (l a)

    \;

    setter :: Lens a b -\<gtr\> b -\<gtr\> a -\<gtr\> a

    setter l b a = peek (l a) b
  </verbatim>

  \;

  And conversely, given a getter and setter we can build a <verbatim|Lens>.

  \;

  <\verbatim>
    mkLens :: (a -\<gtr\> b) -\<gtr\> (b -\<gtr\> a -\<gtr\> a) -\<gtr\> Lens
    a b

    mkLens gtr str = Lens \\a -\<gtr\> Store (\\b -\<gtr\> str b a) a
  </verbatim>

  \;

  However, it is more efficent to define a lens directly as we did in
  <verbatim|nameLens> above.

  Naturally we require the three getter/setter laws to hold for the a lens to
  be valid. There is, however, a more natural way to express these laws in
  this representation, but first we need to define the comonad operations of
  the store comonad.

  Dual to monads, comonads are <verbatim|Functor>s with two operations which
  we call <verbatim|extract> and <verbatim|duplicate>.

  <\verbatim>
    class Functor w =\<gtr\> Comonad w where

    \ \ extract :: w a -\<gtr\> a

    \ \ duplicate :: w a -\<gtr\> w (w a)

    \ \ extend :: (w a -\<gtr\> b) -\<gtr\> w a -\<gtr\> w b

    \ \ extend f = fmap f . duplicate
  </verbatim>

  \;

  Comonads are required to satify three laws, which are dual to the monad
  laws:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<with|mode|text|<verbatim|extract>>\<circ\><with|mode|text|<verbatim|duplicate>>>|<cell|=>|<cell|<with|mode|text|<verbatim|id>>>>|<row|<cell|<with|mode|text|<verbatim|fmap
    extract>>\<circ\><with|mode|text|<verbatim|duplicate>>>|<cell|=>|<cell|<with|mode|text|<verbatim|id>>>>|<row|<cell|<with|mode|text|<verbatim|fmap
    duplicate>> \<circ\><with|mode|text|<verbatim|duplicate>>>|<cell|=>|<cell|<with|mode|text|<verbatim|duplicate>>\<circ\><with|mode|text|<verbatim|duplicate>>>>>>
  </eqnarray*>

  To show that <verbatim|Store b> forms a comonad, we need to define
  <verbatim|fmap>, <verbatim|extend> and <verbatim|duplicate> and prove that
  it satifies the required laws.

  <\verbatim>
    instance Functor (Store i) where

    \ \ fmap f (Store v b) = Store (f . v) b

    \;

    instance Comonad (Store i) where

    \ \ extract (Store v b) = v b

    \ \ duplicate (Store v b) = Store (Store v) b
  </verbatim>

  \;

  Interested readers can find the proof that the comonad laws are satified in
  Appendix<nbsp><inactive|<reference|>>.

  \;

  With the <verbatim|Store> comonad operations in hand, we can state the
  alternative form the lens laws.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<with|mode|text|<verbatim|extract>>\<circ\><with|mode|text|<verbatim|runLens
    l>>>|<cell|=>|<cell|<with|mode|text|<verbatim|id>>>>|<row|<cell|<with|mode|text|<verbatim|duplicate>>
    \<circ\><with|mode|text|<verbatim|runLens
    l>>>|<cell|=>|<cell|<with|mode|text|<verbatim|fmap (runLens
    l)>>\<circ\><with|mode|text|<verbatim|runLens l>>>>>>
  </eqnarray*>

  These two laws are equivalent to the three lense laws. \ Notice that these
  laws are expressed entirely in terms of the comonad functions. \ For any
  comonad <verbatim|w>, any function of type <verbatim|a -\<gtr\> w a> that
  satifies these two laws is called a <em|coalgebra for the <verbatim|w>
  comonad>. \ So lenses are precisely the coalgebras of for the
  <verbatim|Store b> comonad.

  In this representation, the identity lens and lens composition is defined
  as follows with the help of this <verbatim|experiment> function.

  <\verbatim>
    experiment :: Functor f =\<gtr\> (i -\<gtr\> f i) -\<gtr\> Store i a
    -\<gtr\> f a

    experiment f (Store v b) = v \<less\>$\<gtr\> f b

    \;

    instance Category Lens where

    \ \ id = Lens (Store id)

    \ \ Lens l2 . Lens l1 = Lens (experiment l2 . l1)
  </verbatim>

  <subsection|van Laarhoven Lenses>

  The <verbatim|experiment> function completely characterises the
  <verbatim|Store i a> in the sense that

  <verbatim|flip experiment :: Store i a -\<gtr\> forall f. (Functor f)
  =\<gtr\> (i -\<gtr\> f i) -\<gtr\> f a>

  <no-indent>forms a isomorphism between <verbatim|Store i a> and
  <verbatim|forall f. (Functor f) =\<gtr\> (i -\<gtr\> f i) -\<gtr\> f a>.
  \ The inverse of this isomorphism is

  <verbatim|\\f -\<gtr\> f (Store id) :: (forall f. (Functor f) =\<gtr\> (i
  -\<gtr\> f i) -\<gtr\> f a)) -\<gtr\> Store i a>.

  This means that <verbatim|a -\<gtr\> forall f. (Functor f) =\<gtr\> (i
  -\<gtr\> f i) -\<gtr\> f a> is another representation of lenses. \ After
  rearraning the parameters we get the van Laarhoven lens representation.

  <verbatim|type Lens a b = forall f. (Functor f) =\<gtr\> (b -\<gtr\> f b)
  -\<gtr\> a -\<gtr\> f a>

  \;

  The definition of <verbatim|nameLens> in this represenation is

  <\verbatim>
    nameLens :: Lens Person String

    nameLens f (Person name address email) =

    \ \ (\\newName -\<gtr\> Person newName address email) \<less\>$\<gtr\> (f
    name)
  </verbatim>

  \;

  We can easily build a coalgebra of the store comonad from this
  represenation by appealing to the inverse isomorphism. \ 

  \;

  <\verbatim>
    mkCoalgebra :: Lens a b -\<gtr\> a -\<gtr\> Store b a

    mkCoalgebra l = l (Store id)
  </verbatim>

  \;

  Conversely, given a coalgebra of the store comonad we can build a van
  Laarhoven lens using <verbatim|experiment>.

  \;

  <\verbatim>
    fromCoalgebra :: (a -\<gtr\> Store b a) -\<gtr\> Lens a b

    fromCoalgebra l f = experiment f . l
  </verbatim>

  \;

  There lens laws can convently expressed in this <em|van Laarhoven>
  representation as well.

  <\eqnarray*>
    <tformat|<table|<row|<cell|l <with|mode|text|<verbatim|Identity>>>|<cell|=>|<cell|<with|mode|text|<verbatim|Identity>>>>|<row|<cell|l
    <around*|(|<with|mode|text|<verbatim|Compose>>\<circ\><with|mode|text|<verbatim|fmap>>
    g\<circ\>f|)>>|<cell|=>|<cell|<with|mode|text|<verbatim|Compose>>\<circ\><with|mode|text|<verbatim|fmap>>
    <around*|(|l g|)>\<circ\>l f>>>>
  </eqnarray*>

  Interested readers can find the proof that these van Laarhoven laws are
  satified in Appendix<nbsp><inactive|<reference|>>.

  One nice property of the van Laarhoven lens is that the identity and
  composition of lenses are simply the prelude functions.

  <\verbatim>
    id :: Lens a a

    (.) :: Lens a b -\<gtr\> Lens b c -\<gtr\> Lens a c
  </verbatim>

  \;

  The caveat is that the composition function is reversed from the usual
  order of composition. \ However, this reversed order actually works very
  well in practice since it matches the usual order of projections in
  tradition order found in programming. <with|color|red|Need examples, and
  this should probably all be done at the beginning of this section.>

  <subsection|Lenses and the State Monad>

  Lenses work extraordinarily well with the state monad. Lenses let you focus
  in on and alter particular fields of your state allowing you to manipulate
  them.

  \;

  <\verbatim>
    access :: Lens a b -\<gtr\> State a b

    access l = do s \<less\>- get

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ return (s^.l)

    \;

    (%=) :: Lens a b -\<gtr\> b -\<gtr\> State a ()

    l %= x = modify (l %~ b)
  </verbatim>

  \;

  <\with|color|red>
    Example needed.
  </with>

  \;

  We can even define C-style imperitive update functions which allow us to
  write imperative looking code where lenses behave like LHS variables

  \;

  <\verbatim>
    (+=), (-=), (*=) :: Num b =\<gtr\> Lens a b -\<gtr\> b -\<gtr\> State a
    ()

    l += x = l %= (+ x)

    l -= x = l %= (subtract x)

    l *= x = l %= (* x)
  </verbatim>

  \;

  However the real power of lenses lies in the <verbatim|focus> function.

  \;

  <\verbatim>
    focus :: Lens a b -\<gtr\> State b c -\<gtr\> State a c

    focus l (State s) = State (l %%= s)
  </verbatim>

  <with|color|red|I hate the name <verbatim|%%=>.>

  \;

  The <verbatim|focus> function lets you promote a state transformation on a
  local state of type <verbatim|b> to a state transformation on a global
  state of type <verbatim|a> using a <verbatim|Lens a b>. \ This lets users
  large record for a global state for their state transformer program, but
  focus in on smaller and smaller fragments of this global state for
  subroutines of the state transformer. \ The type system then ensures that
  these subroutines do not access parts of the global state beyond what they
  are allowed to access.

  <section|Lens Families>

  A shortcoming of lenses as defined in the previous section is that setting
  a field can never change the type of the record. Consider the following
  simple pair type

  <verbatim|data Pair a b = Pair a b>

  \;

  The getter and setters of the first component are defined as

  <\verbatim>
    get_first :: Pair a b -\<gtr\> a

    get_first (Pair x y) = x

    \;

    set_first :: a -\<gtr\> Pair a b -\<gtr\> Pair a b

    set_first x (Pair _ y) = Pair x y
  </verbatim>

  \;

  This definition <verbatim|set_first> cannot change the type of the first
  component. \ However, type inference gives a more general type for
  <verbatim|set_first> which allows the type of the first component to be
  changed.

  <verbatim|set_first :: a' -\<gtr\> Pair a b -\<gtr\> Pair a' b>

  \;

  We can give a more general definition of lenses that allows for such setter
  function to change the type parameters of record type.

  <\verbatim>
    data LensFamily a a' b b' = LensFamily { getter : a -\<gtr\> b

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ ;
    setter : b' -\<gtr\> a -\<gtr\> a'

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }
  </verbatim>

  \;

  By generalizing the store comonad to the indexed store comonad, we can
  create lens representation as a coalgebroid for the indexed store comonad.

  <\verbatim>
    data IStore i j a = IStore { peek :: j -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ , pos :: i

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }

    \;

    instace Functor (IStore i j) where

    \ \ fmap f (IStore v b) = IStore (f . v) b

    \;

    extract :: IStore i i a -\<gtr\> a

    extract (IStore v b) = v b

    \;

    duplicate :: IStore i j a -\<gtr\> IStore i k (IStore k j a)

    duplicate (IStore v b) = IStore (IStore v) b

    \;

    newtype LensFamily a a' b b' =

    \ \ LensFamily { runLensFamily : a -\<gtr\> IStore b b' a' }
  </verbatim>

  \;

  The van Laarhoven represention can be generalized the same way

  <\verbatim>
    type LensFamily a a' b b' =

    \ \ forall f. (Functor f) =\<gtr\> (b -\<gtr\> f b') -\<gtr\> a -\<gtr\>
    f a'
  </verbatim>

  <section|Traversals>

  No matter what representation, a valid <verbatim|Lens a b> value picks out
  a single substructure of type <verbatim|b> from the type <verbatim|a>.
  \ There is a related structure we call <verbatim|Traversal a b> that picks
  out many substructures of type <verbatim|b> from the type <verbatim|a>.

  <verbatim|type Traversal a b = forall f. (Applicative f) =\<gtr\> (b
  -\<gtr\> f b) -\<gtr\> a -\<gtr\> f a>

  \;

  For example, we can make a <verbatim|Traversal Person String> that
  references all three fields with the following.

  <\verbatim>
    personTraversal :: Traversal Person String

    personTraversal f (Person name address email) =

    \ \ Person \<less\>$\<gtr\> f name \<less\>*\<gtr\> f address
    \<less\>*\<gtr\> f email
  </verbatim>

  \;

  This traversal can be used, for example, to produce a list strings from a
  <verbatim|Person> value.

  \;

  <\verbatim>
    toListOf :: Traversal a b -\<gtr\> a -\<gtr\> [b]

    toListOf t = getConst . t (Const . (:[]))\ 

    \;

    personInfo :: Person -\<gtr\> [String]

    personInfo = toListOf personTraversal
  </verbatim>

  \;

  We can also modify a <verbatim|Person> by lower-casing each field.

  \;

  <\verbatim>
    (%~) :: Traversal a b -\<gtr\> (b -\<gtr\> b) -\<gtr\> (a -\<gtr\> a)

    t %~ f = runIdentity . t (Identity . f)

    \;

    lowerPerson :: Person -\<gtr\> Person

    lowerPerson = personTraversal %~ (map lowerCase)
  </verbatim>

  \;

  An we can run through the traversal with a monadic map.

  \;

  <\verbatim>
    mapMOf :: (Monad m) =\<gtr\> Traversal a b -\<gtr\> (b -\<gtr\> m b)
    -\<gtr\> (a -\<gtr\> m a)

    mapMOf t f = unwrapMonad . t (WrapMonad . f)

    \;

    countChars :: Person -\<gtr\> Writer (Sum Integer) Person

    countChars = mapMOf personTraversal countString

    \ \ where

    \ \ \ \ countString :: String -\<gtr\> Writer (Sum Integer) String

    \ \ \ \ countString s = do tell (Sum (length s))

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ return s
  </verbatim>

  \;

  Like lenses, in order for a traversal value to be valid, it must satify two
  laws. \ The laws are exactly the same as the laws for lenses.

  <\eqnarray*>
    <tformat|<table|<row|<cell|t <with|mode|text|<verbatim|Identity>>>|<cell|=>|<cell|<with|mode|text|<verbatim|Identity>>>>|<row|<cell|t
    <around*|(|<with|mode|text|<verbatim|Compose>>\<circ\><with|mode|text|<verbatim|fmap>>
    g\<circ\>f|)>>|<cell|=>|<cell|<with|mode|text|<verbatim|Compose>>\<circ\><with|mode|text|<verbatim|fmap>>
    <around*|(|t g|)>\<circ\>t f>>>>
  </eqnarray*>

  These laws ensure that a traversal is a ordered sequence of zero or more
  disjoint substructures of type <verbatim|b> of a structure of type
  <verbatim|a>.

  Similar to lenses, we can generalize traversals to allow update functions
  to change the type parameters of a structure.

  <\verbatim>
    type TraversalFamily a a' b b' =

    \ \ forall f. (Applicative f) =\<gtr\> (b -\<gtr\> f b') -\<gtr\> a
    -\<gtr\> f a'
  </verbatim>

  For example, we can create a traversal for both fields of our
  <verbatim|Pair> type that allows updates to change both types together.

  <\verbatim>
    both :: TraversalFamily (Pair a a) (Pair a' a') a a'

    both f (Pair x y) = Pair \<less\>$\<gtr\> f x \<less\>*\<gtr\> f y
  </verbatim>

  \;

  <\equation*>
    <with|mode|text|<verbatim|(both %~ length) (``Hello'',
    ``World!'')>>=<with|mode|text|<verbatim|(6,7)>>
  </equation*>

  The <verbatim|Traversable> class provides a canoncial traversal for
  containers instantiating it. \ Recall the <verbatim|traverse> function.

  <\verbatim>
    traverse :: (Traversal t, Applicative f) =\<gtr\> (a -\<gtr\> f a)
    -\<gtr\> t a -\<gtr\> f (t a)
  </verbatim>

  \;

  The signature for the <verbatim|traverse> function fits our traversal
  family.

  \;

  <verbatim|traverse :: (Traversal t) =\<gtr\> TraversalFamily a b (t a) (t
  b)>

  \;

  <with|color|red|Something about <verbatim|Traversal> laws.> Therefore
  <verbatim|traverse> can always be used as a <verbatim|TraversalFamily>.

  <subsection|Composing Lenses and Traversals>

  Recall that a lens is a single reference and a traversal is a sequence of
  zero or more disjoint references. Therefore every lens is a special case of
  a traversal. \ This means that we can compose a traversal and a lens,
  considered as a traversal of length 1, to get a traversal.

  This is the situtation where the van Laarhoven represenation really shines.
  \ Rather than having to cast a lens to a traversal, we can directly compose
  lenses and traversals with the composition operation. Because we have used
  type synonyms instead of newtype, the <verbatim|Functor> constraint of the
  lens is combined by the type system with the <verbatim|Applicative>
  constraint of the traversable, yeilding an <verbatim|Applicative>
  constraint for the overall combination. \ Consider the following lens and
  traversal and their composition.

  <\verbatim>
    _1 :: LensFamily (a, b) (a', b) a a'

    traverse :: TraversalFamily [a] [a'] a a'

    traverse._1 :: TraversalFamily [(a,b)] [(a',b)] a a'
  </verbatim>

  \;

  Then we can use this composition to modify the first component of every
  value in a list of pairs.

  <\equation*>
    <with|mode|text|<verbatim|traverse._1 \<less\>~ (^2) $ [(2, ``Hello''),
    (3, ``World'')]>>=<with|mode|text|<verbatim|[(4, ``Hello''), (9,
    ``World'')]>>
  </equation*>

  <subsection|Kleene Stores>

  <with|color|red|This turns out to be kinda complicated; it should probably
  be relegated to an appendix.>

  We can represent traversals as a coalgebroids of a variation of the store
  comonad. \ First recall the definition of the store comonad.

  <\verbatim>
    data Store i a = Store { peek :: i -\<gtr\> a

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ ,
    <with|font-series|bold|pos :: i>

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }
  </verbatim>

  The associated store comonad transformer is defined as.

  <\verbatim>
    data StoreT i w a = StoreT { peekT :: w (i -\<gtr\> a)

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ , posT :: i

    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ }

    \;

    instance Functor w =\<gtr\> Functor (StoreT i w) where

    \ \ fmap f (StoreT v b) = StoreT (fmap (f .) v) b

    \;

    instance Comonad w =\<gtr\> Comonad (StoreT i w) where

    \ \ extract (StoreT v b) = extract v b

    \ \ duplicate (StoreT v b) = StoreT (extend StoreT v) b
  </verbatim>

  \;

  We also note that the sum of two comonads is a comonad

  \;

  <\verbatim>
    newtype (f1 :+: f2) a = SumF { getSumF :: Either (f1 a) (f2 a) }

    \;

    instance (Functor w1, Functor w2) =\<gtr\> Functor (w1 :+: w2) where

    \ \ fmap f (SumF x) = SumF ((fmap f +++ fmap f) x)

    \;

    instance (Comonad w1, Comonad w2) =\<gtr\> Comonad (w1 :+: w2) where

    \ \ extract (SumF x) = either extract extract x

    \ \ duplicate (SumF (Left x)) = SumF . Left $ extend (SumF . Left) x

    \ \ duplicate (SumF (Right x)) = SumF . Right $ extend (SumF . Right) x
  </verbatim>

  \;

  and the <verbatim|Identity> functor is a comonad.

  \;

  <\verbatim>
    instance Comonad Identity where

    \ \ extract (Identity x) = x

    \ \ duplicate x = Identity x
  </verbatim>

  \;

  The Kleene store is defined as the infinite sum of itereated store
  trasformers

  \;

  <\equation*>
    <with|mode|text|<verbatim|KleeneStore
    i>>=<with|mode|text|<verbatim|Identity :+: StoreT i Identity :+: StoreT i
    (StoreT i Identity) :+: ...>>
  </equation*>

  Naturally we define this recursively instead

  <\verbatim>
    newType KleeneStore i a = KleeneStore

    \ \ { runKleeneStore :: (Identity :+: StoreT i (KleeneStore i)) a }

    \;

    instance Functor (KleeneStore i) where

    \ \ fmap f (KleeneStore k) = KleeneStore (fmap f k)

    \;

    instance Comonad (KleeneStore i) where

    \ \ extract (KleeneStore k) = extract k

    \ \ dupicate (KleeneStore k) = KleeneStore (extend KleeneStore k)
  </verbatim>

  \;

  <with|color|red|Describe what a Kleene store means.>

  \;

  Importantly, Kleene stores forms an applicative functor .

  \;

  <\verbatim>
    instance Applicative (KleeneStore i) where

    \ \ pure x = KleeneStore (SumF (Left (Identity x)))

    \ \ (KleeneStore (SumF (Left (Identity f)))) \<less\>*\<gtr\> x = fmap f
    x

    \ \ (KleeneStore (SumF (Right (StoreT v b))) \<less\>*\<gtr\> x =

    \ \ \ \ \ Kleenestore (SumF (Right (StoreT (flip \<less\>$\<gtr\> v
    \<less\>*\<gtr\> x) b)))
  </verbatim>

  \;

  A function called <verbatim|research> performs an analgous role to
  <verbatim|experiment> for Kleene stores; however <verbatim|research>
  requires an applicative functor.

  \;

  <\verbatim>
    research :: Applicative f =\<gtr\> (i -\<gtr\> f i) -\<gtr\> KleeneStore
    i a -\<gtr\> f a

    research _ (KleeneStore (SumF (Left (Identity x)))) = pure x

    research f (KleeneStore (SumF (Right (StoreT v b))) = f b
    \<less\>**\<gtr\> research f v
  </verbatim>

  \;

  The <verbatim|research> function completely characterises a Kleene store in
  the sense that

  \;

  <verbatim|flip research :: KleeneStore i a -\<gtr\> forall f. Applicative f
  =\<gtr\> (i -\<gtr\> f i) -\<gtr\> f a>

  forms an isomorphism between <verbatim|KleeneStore i a> and
  <verbatim|forall f. Applicative f -\<gtr\> (i -\<gtr\> f i) -\<gtr\> f a>.
  \ The inverse of this isomorphis is provided by

  \;

  <verbatim|\\f -\<gtr\> f (KleeneStore . SumF . Right . StoreT pure) ::
  (forall f. Applicative f =\<gtr\> (i -\<gtr\> f i) -\<gtr\> f a) -\<gtr\>
  KleeneStore i a>

  <\with|color|red>
    Ought to define

    <\verbatim>
      battery :: KleeneStore i (i -\<gtr\> a) -\<gtr\> i -\<gtr\> KleeneStore
      i a

      battery f = KleeneStore . SumF . Right . StoreT f
    </verbatim>

    first.
  </with>

  \;

  This isomorphism implies we an alternative representation of
  <verbatim|Traversal a b> as a coalgebra <verbatim|a -\<gtr\> KleeneStore b
  a>. Such a coalgebra can be generated from a traversal with the following

  \;

  <\verbatim>
    coalgTraverse :: Traversal a b -\<gtr\> a -\<gtr\> KleeneStore b a

    coalgTraverse t = t (battery (pure id))
  </verbatim>

  \;

  Conversely, a traversal can be generated by such a coalgebra by the
  following.

  \;

  <\verbatim>
    fromCoalg :: (a -\<gtr\> KleeneStore b a) -\<gtr\> Traversal a b

    fromCoalg t f = research f . t
  </verbatim>

  <section|Mirrored Lenses>

  <section|Conclusion>

  <section|Acknowledgements>

  Wren for the name of Kleene store.
</body>

<\initial>
  <\collection>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|0|1>>
    <associate|auto-10|<tuple|3|5>>
    <associate|auto-11|<tuple|4|6>>
    <associate|auto-12|<tuple|4.1|6>>
    <associate|auto-13|<tuple|4.2|?>>
    <associate|auto-14|<tuple|5|?>>
    <associate|auto-15|<tuple|6|?>>
    <associate|auto-16|<tuple|7|?>>
    <associate|auto-2|<tuple|1|1>>
    <associate|auto-3|<tuple|2|1>>
    <associate|auto-4|<tuple|2.1|2>>
    <associate|auto-5|<tuple|2.2|2>>
    <associate|auto-6|<tuple|2.3|3>>
    <associate|auto-7|<tuple|2.4|4>>
    <associate|auto-8|<tuple|2.5|4>>
    <associate|auto-9|<tuple|2.6|4>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|0<space|2spc>Licence>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Lenses>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Using Lenses
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Combining Lenses
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1.5fn>|2.3<space|2spc>Coalgebra of the Store
      Comonad <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1.5fn>|2.4<space|2spc>van Laarhoven Lenses
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|2.5<space|2spc>Lenses and the State Monad
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Lens
      Families> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Traversals>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>Kleene Stores
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Mirrored
      Lenses> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Conclusion>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Acknowledgements>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>