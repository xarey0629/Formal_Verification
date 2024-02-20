
# (Linear) Temporal (Logic) Expressions

# kind =
# G | G0 | F | X | and | or | not | implies | var 
# G G0 F X not:  have arg1 field
# and or implies: have arg2 field also
# var: has name field

class TExp:
    def __init__(self, kind):
        self.kind = kind

    def unop(self, kind):
        te = TExp(kind)
        te.arg1 = self
        return te
        
    def binop(self, r_arg, kind):
        te = TExp(kind)
        te.arg1 = self
        te.arg2 = r_arg
        return te

    # prefix ~
    def __invert__(self): return self.unop('not')

    # infix &
    def __and__(self, r_arg): return self.binop(r_arg, 'and')

    # infix |
    def __or__(self, r_arg):  return self.binop(r_arg, 'or')

    # infix >> (used for implication)
    def __rshift__(self, r_arg): return self.binop(r_arg, 'implies')

    # What's returned by str(t) when t is a TExp
    def __str__(self):
        if self.kind == 'G':
            return 'G ' + str(self.arg1)
        elif self.kind == 'G0':
            return 'G0 ' + str(self.arg1)
        elif self.kind == 'F':
            return 'F ' + str(self.arg1)
        elif self.kind == 'X':
            return 'X ' + str(self.arg1)
        elif self.kind == 'and':
            return '(' + str(self.arg1) + ' & ' + str(self.arg2) + ')'
        elif self.kind == 'or':
            return '(' + str(self.arg1) + ' | ' + str(self.arg2) + ')'
        elif self.kind == 'implies':
            return '(' + str(self.arg1) + ' >> ' + str(self.arg2) + ')'
        elif self.kind == 'not':
            return '~ ' + str(self.arg1) 
        elif self.kind == 'var':
            return self.name 
        else:
            raise Exception("Unrecognised kind: " + self.kind)

    # What's returned by repr(t) when t is a TExp
    def __repr__(self):
        if self.kind == 'G':
            return 'G(' + repr(self.arg1) + ')'
        elif self.kind == 'G0':
            return 'G0(' + repr(self.arg1) + ')'
        elif self.kind == 'F':
            return 'F(' + repr(self.arg1) + ')'
        elif self.kind == 'X':
            return 'X(' + repr(self.arg1) + ')'
        elif self.kind == 'and':
            return '(' + repr(self.arg1) + ' & ' + repr(self.arg2) + ')'
        elif self.kind == 'or':
            return '(' + repr(self.arg1) + ' | ' + repr(self.arg2) + ')'
        elif self.kind == 'implies':
            return '(' + repr(self.arg1) + ' >> ' + repr(self.arg2) + ')'
        elif self.kind == 'not':
            return '~ ' + repr(self.arg1) 
        elif self.kind == 'var':
            return 'Var(\'' + self.name + '\')'
        else:
            raise Exception("Unrecognised kind: " + self.kind)

# Defined outside class because we prefix syntax.

def F(phi): return phi.unop('F')

def G(phi): return phi.unop('G')

def G0(phi): return phi.unop('G0')

def X(phi): return phi.unop('X')

def Var(name1):
    te = TExp('var')
    te.name = name1
    return te

