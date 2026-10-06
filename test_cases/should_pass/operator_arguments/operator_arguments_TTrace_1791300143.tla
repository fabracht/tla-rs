---- MODULE operator_arguments_TTrace_1791300143 ----
EXTENDS Sequences, TLCExt, operator_arguments, Toolbox, Naturals, TLC

_expression ==
    LET operator_arguments_TEExpression == INSTANCE operator_arguments_TEExpression
    IN operator_arguments_TEExpression!expression
----

_trace ==
    LET operator_arguments_TETrace == INSTANCE operator_arguments_TETrace
    IN operator_arguments_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        x = (3)
        /\
        y = (0)
    )
----

_init ==
    /\ x = _TETrace[1].x
    /\ y = _TETrace[1].y
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ x  = _TETrace[i].x
        /\ x' = _TETrace[j].x
        /\ y  = _TETrace[i].y
        /\ y' = _TETrace[j].y

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("operator_arguments_TTrace_1791300143.json", _TETrace)

=============================================================================

 Note that you can extract this module `operator_arguments_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `operator_arguments_TEExpression.tla` file takes precedence 
  over the module `operator_arguments_TEExpression` below).

---- MODULE operator_arguments_TEExpression ----
EXTENDS Sequences, TLCExt, operator_arguments, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `operator_arguments` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        x |-> x
        ,y |-> y
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_xUnchanged |-> x = x'
        
        \* Format the `x` variable as Json value.
        \* ,_xJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(x)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_xModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].x # _TETrace[s-1].x
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE operator_arguments_TETrace ----
\*EXTENDS IOUtils, operator_arguments, TLC
\*
\*trace == IODeserialize("operator_arguments_TTrace_1791300143.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE operator_arguments_TETrace ----
EXTENDS operator_arguments, TLC

trace == 
    <<
    ([x |-> 0,y |-> 0]),
    ([x |-> 1,y |-> 0]),
    ([x |-> 2,y |-> 0]),
    ([x |-> 3,y |-> 0])
    >>
----


=============================================================================

---- CONFIG operator_arguments_TTrace_1791300143 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Tue Oct 06 08:22:23 PDT 2026