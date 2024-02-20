# Formal Verification 2023-24
# Coursework 2

# BMC with Z3

from z3 import *
from texp import *

####### COMPLETE (Section 2.1) #######
def nnf(f):
    if f.kind == 'not':
        inner = f.arg1
        if inner.kind == 'and':
            # De Morgan's Law: ¬(A ∧ B) ≡ ¬A ∨ ¬B
            return nnf(inner.arg1.__invert__()).__or__(nnf(inner.arg2.__invert__()))
        
        elif inner.kind == 'or':
            # De Morgan's Law: ¬(A ∨ B) ≡ ¬A ∧ ¬B
            return nnf(inner.arg1.__invert__()).__and__(nnf(inner.arg2.__invert__()))
        
        elif inner.kind == 'implies':
            # ¬(p ⇒ q) ≡ ¬p ∨ q
            return nnf(inner.arg1).__and__(nnf(inner.arg2.__invert__()))
        
        elif inner.kind == 'X':
            return X(nnf(inner.arg1.__invert__()))
        
        elif inner.kind == 'F':
            return G(nnf(inner.arg1.__invert__()))
        
        elif inner.kind == 'G':
            return F(nnf(inner.arg1.__invert__()))
        
        elif inner.kind == 'G0':
            return F(nnf(inner.arg1.__invert__()))
        
        else:
         return f  # Atomic proposition or other operators, no change needed
    
    elif f.kind == 'and':
        return nnf(f.arg1) & nnf(f.arg2)
    
    elif f.kind == 'or':
        return nnf(f.arg1) | nnf(f.arg2)
    
    elif f.kind == 'implies':
        # (p ⇒ q) ≡ ¬p ∨ q
        return nnf(f.arg1.__invert__()).__or__(nnf(f.arg2))
    
    elif f.kind == 'F':
        return F(nnf(f.arg1))
    
    elif f.kind == 'G':
        return G(nnf(f.arg1))
    
    elif f.kind == 'G0':
        return G0(nnf(f.arg1))
    
    elif f.kind == 'X':
        return X(nnf(f.arg1))
        
    else:
        return f  # Atomic proposition or other operators, no change needed
    
# Test NNF Cases
# fmla = ~ X(Var('b') | Var('c') & Var('d'))
# fmla = ~ ~ (Var('b'))
# fmla = ~(Var('b')) & ~(Var('c'))
# fmla = G0(~((Var('b') >> (Var('c')))))
# print(fmla.kind)
# fmla = ~X(Var('b'))
# fmla = G0(Var('b') >> Var('c'))
# print("NNF", nnf(fmla))

# Use this function in ltl_to_prop, var case.
def add_index(name, index):
    return "%s_%d" % (name, index)

####### COMPLETE (Section 2.2) ####### 
def ltl_to_prop(l, k, i, f):
    
    if f.kind == 'var':  # Atomic proposition
        return Bool(add_index(f.name, i))

    elif f.kind == 'and':
        return And(ltl_to_prop(l, k, i, f.arg1), ltl_to_prop(l, k, i, f.arg2))

    elif f.kind == 'or':
        return Or(ltl_to_prop(l, k, i, f.arg1), ltl_to_prop(l, k, i, f.arg2))

    elif f.kind == 'not':
        return Not(ltl_to_prop(l, k, i, f.arg1))

    elif f.kind == "X":
        if i == k - 1 and l == None:
            return False
        if i < k - 1:
            return ltl_to_prop(l, k, i + 1, f.arg1)
        else:
            return ltl_to_prop(l, k, l, f.arg1)  # loop back
    
    elif f.kind == 'F':
        if l == None:
            return Or([ltl_to_prop(l, k, j, f.arg1) for j in range(i, k)])
        else:
            return Or([ltl_to_prop(l, k, j, f.arg1) for j in range(min(l, i), k)])

    elif f.kind == "G":
        if l == None:
            return False
        else:
            return And([ltl_to_prop(l, k, j, f.arg1) for j in range(min(l, i), k)])
        
    elif f.kind == 'G0':
        if l == None:
            return And([ltl_to_prop(l, k, j, f.arg1) for j in range(0, k - 1)])
        else:
            return And([ltl_to_prop(l, k, j, f.arg1) for j in range(0, k)])
        
    return Exception("Unrecognised kind durin transform ltl to propositional logic: " + f.kind)  # Handle Exception

# Test Cases
# def ltl_to_prop(l, k, i, f):
# print(ltl_to_prop(0, 5, 1, nnf(~G(Var('b')))))


####### COMPLETE (Section 2.3) ####### 
#
# Questions about the structure of the ltl_to_prop translation function
#
# Q1: About G0
# A1: Since G0 means it starts from the initial state s_0, it checks all the states in the path(from s_0 to s_k-1) T holds]. 
#
#
#
# Q2: About G in the prefix case
# A2: Cause '-' means the path starts from s_0 and ends in s_k-1, which is a finite path with no loop, and no future states for phi to hold.
#
#
#
# Q3: About X at k - 1 in the loop case
# A3: Cause the next state of k-1 will loop back to state s_l.
#
#
#
# Q4: About X at k - 1 in the prefix case
# A4: Cause '-' means the finite path starts from s_0 to s_k-1. When i = k - 1, the next state doesn't exist on the path.
#
#
#
# Q5: About  F, G in the loop case, with j = min(i,l)
# A5: Cause the formula may be satisfied outside(before going into loop) or inside the loop. 
#     We need to check all states from and including s_i onwards, and all states in the loop.
#
#
#
#

    
# Get the name of the state at position index in the model mod
def extract_state(mod, vars, states, index):
    ivars = [Bool(add_index(v, index)) for v in vars]
    ivar_vals = [mod[ivar] for ivar in ivars]
    true_vars = [var for var,val in zip(vars,ivar_vals) if val]
    return states[' '.join(true_vars)]

# Extract out the sequence of states in the model mod
def extract_path(mod, vars, states, k):
    return ' '.join([extract_state(mod, vars, states, i) for i in range(0,k)])


####### COMPLETE (Section 2.4) ####### 
def setup_bmc(sys, fmla, l, k):
    vars, states, init, trans = sys
    s = Solver()

    # print("vars:", vars)
    # print("states:", states)
    # print("init:", init)
    # print("trans:", trans)
    # print("fmla:", fmla)
    # print("nnf", nnf(fmla))
    
    # COMPLETE THIS ASSIGNMENT
    full_ltl_fmla = nnf(init) & nnf(G0(trans)) & nnf(fmla)
    # Test
    # print("Full_LTL_Formula:", full_ltl_fmla)
    
    prop_fmla = ltl_to_prop(l, k, 0, full_ltl_fmla)
    # print("Prop_fmla:", prop_fmla)
    
    s.add(prop_fmla)
    return s

def run_bmc(sys, fmla, l, k):
    s = setup_bmc(sys, fmla, l, k)
    result = s.check()
    if result == sat:
        mod = s.model()
        vars, states, init, trans = sys
        path = extract_path(mod, vars, states, k)
    else:
        path = ''
    return result, path

# Try all values of l, return first if any which gives sat
def run_bmc_full(sys, fmla, k):

    s = setup_bmc(sys, fmla, None, k)
    result = s.check()
    
    vars, states, init, trans = sys
    # 
    if result == sat:
        mod = s.model()
        path = extract_path(mod, vars, states, k)
        return print(sat, None, path)
    
    for l in range(0,k):
        s = setup_bmc(sys, fmla, l, k)
        result = s.check()
        # 
        if result == sat:
            mod = s.model()
            path = extract_path(mod, vars, states, k)
            return print(sat, l, path)
    return print(unsat)


################################################
# System 1:
# 2 state system described by SMV program in Section 2.2
vars1 = 'b'
states1 = {'':'s1', 'b':'s2'}

s1 = ~ Var('b')
s2 = Var('b')
    
init1 = s1
trans1 = (s1 >> X(s2)) & (s2 >> X(s1))

sys1 = vars1, states1, init1, trans1

################################################
# Tests of System 1

# Check that G(F(s1)) is valid
run_bmc_full(sys1, ~ G(F(s1)), 5)
# unsat

# Check that there exists path such that F(s2 & X(s1)), bounds 1
run_bmc_full(sys1, F(s2 & X(s1)), 1)
# unsat

# Check that there exists path such that F(s2 & X(s1)), bounds 2
run_bmc_full(sys1, F(s2 & X(s1)), 2)
# (sat, 0, 's1 s2')

# Check that there exists path such that F(s2 & X(s1)), bounds 3
run_bmc_full(sys1, F(s2 & X(s1)), 3)
# (sat, None, 's1 s2 s1')


################################################
# System 2:
# 4 state system described in Section 2.5.

vars2 = 'a b'
states2 = {'':'q1', 'b':'q2', 'a':'q3', 'a b':'q4'}

####### COMPLETE (Section 2.5) ####### 
q1 = (~ Var('a') & ~ Var('b'))
q2 = (~ Var('a') & Var('b'))
q3 = (Var('a') & ~ Var('b'))
q4 = (Var('a') & Var('b'))


####### COMPLETE (Section 2.5) ####### 
init2 = q3
# trans2 = ((q3 >> q4) | (q3 >> q1) | (q3 >> q2)) & (q4 >> q3) & (q2 >> q2) & (q1 >> q2)
# trans2 = ((q3 >> q4) & (q3 >> q1) & (q3 >> q2)) & (q4 >> q3) & (q2 >> q2) & (q1 >> q2)
trans2 = (q3 >> X(q4 | q1 | q2)) & (q4 >> X(q3)) & (q2 >> X(q2)) & (q1 >> X(q2))


sys2 = vars2, states2, init2, trans2


# ################################################
# # Tests of System 2

# ####### COMPLETE (Section 2.6) #######
# # Test 1: Check that F(a & !b) is sat, bounds 1
run_bmc_full(sys2, F(q3), 1)
# # (sat, None, 'q3')

# # Test 2: Check that F(G(!a & b)) is sat, bounds 2, 3, 4, ... N
run_bmc_full(sys2, F(G(q2)), 2)
# (sat, 1, 'q3 q2')

# # Test 3: Check that there doesn't exist a path satisfying F(!a & !b ), bounds 1
run_bmc_full(sys2, F(q1), 1)
# # unsat

# # Test 4: Check that there exists a path satisfying F(!a & !b), bounds 2
run_bmc_full(sys2, F(q1), 2)
# (sat, None, 'q3 q1')

# # Test 5: Check that there exists a path satisfying F(a & b), bounds 2
run_bmc_full(sys2, F(q4), 2)
# # (sat, None, 'q3 q4')

# # Test 6: Check that there doesn't exist a path satisfying G(a & b), bounds 3
run_bmc_full(sys2, G(q4), 3)
# # unsat

# # Test 7: Check that there exists a path satisfying G(F(a & b)), bounds 2
run_bmc_full(sys2, G(F(q4)), 2)
# # (sat, 0, 'q3 q4')

# # Test 8: Check that there exists a path satisfying F(G(q2)) & F(G(q2)) >> F((~(q1 | q3 | q4))), bounds 2
run_bmc_full(sys2, F(G(q2)) & F(G(q2)) >> F((~(q1 | q3 | q4))), 2)
# # (sat, 1, 'q3 q2')

# # Test 9: Check that there exists a path satisfying X(q1) & F(G((q2))), bounds 3
run_bmc_full(sys2, X(q1) & F(G((q2))), 3)
# # (sat, 2, 'q3 q1 q2')

# # Test 10: Check that there exists a path satisfying F(q4) & F(q1) & F(q1) >> F(G(q2)), bounds 5
run_bmc_full(sys2, F(q4) & F(q1) & F(q1) >> F(G(q2)), 5)
# # (sat, 4, 'q3 q4 q3 q1 q2')


# EOF
