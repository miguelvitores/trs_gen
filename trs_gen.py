import random
import sys
import os

curr_idv = 0
curr_idf = 0


names_defined_symbs = {
    "f": 0,
    "g": 0,
    "h": 0
}

names_constructor_symbs = {
    "a": 0,
    "b": 0,
    "c": 0,
    "d": 0,
    "e": 0
}

names_vars = {
    "x": 0,
    "y": 0,
    "z": 0
}


def initialize_names():
    global names_vars, names_defined_symbs, names_constructor_symbs
    names_vars = {k: 0 for k, v in names_vars.items()}
    names_defined_symbs = {k: 0 for k, v in names_defined_symbs.items()}
    names_constructor_symbs = {k: 0 for k, v in names_constructor_symbs.items()}


class Term:
    def __init__(self, tid, args=None):
        self.tid = tid
        self.args = args

    def to_str(self):
        if self.args is None:
            return "{0}".format(self.tid.name)
        else:
            return "{0}({1})".format(self.tid.name, ",".join([a.to_str() for a in self.args]))


class Id:
    def __init__(self, name):
        self.name = name
        self.idn = 0


def get_curr_idv():
    global curr_idv
    curr_idv += 1
    return curr_idv


def get_curr_idf():
    global curr_idf
    curr_idf += 1
    return curr_idf


class IdV (Id):
    def __init__(self, name):
        super().__init__(name)
        self.idn = get_curr_idv()

    def to_str(self):
        return self.name


class IdF (Id):
    def __init__(self, name, arity):
        super().__init__(name)
        self.arity = arity
        self.mu = [a + 1 for a in range(self.arity)]
        self.idn = get_curr_idf()

    def to_str(self):
        return self.name + " " + ", ".join([str(m) for m in self.mu])

    def rand_mu(self):
        a = [a + 1 for a in range(self.arity)]
        random.seed()
        random.shuffle(a)
        k = random.randint(0, len(a))
        self.mu = a[:k]
        self.mu.sort()

    def trs_mu(self):
        self.mu = [a + 1 for a in range(self.arity)]


class IdG (IdF):
    def __init__(self, name, arity=0):
        super().__init__(name, arity)


class Rule:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def to_str(self):
        return "{0} -> {1}".format(self.lhs.to_str(), self.rhs.to_str())


class TRS:
    def __init__(self, def_symbs, const_symbs, variables, rules):
        self.def_symbs = def_symbs
        self.const_symbs = const_symbs
        self.variables = variables
        self.rules = rules

    def to_rand_cstrs(self):
        for d in self.def_symbs:
            d.rand_mu()

    def to_trs(self):
        for d in self.def_symbs:
            d.trs_mu()

    def to_str(self):
        st = \
            "(VAR {0})\n" \
            "(REPLACEMENT-MAP\n" \
            "({1})\n" \
            ")\n" \
            "(RULES\n" \
            "\t{2}\n" \
            ")"
        return st.format(" ".join([v.to_str() for v in self.variables]),
                         ")\n(".join([s.to_str() for s in self.def_symbs | self.const_symbs]),
                         "\n\t".join([r.to_str() for r in self.rules]))


def symbs_used(rules):
    defined_symbs = set()
    constr_symbs = set()
    variables = set()
    for r in rules:
        defined_symbs = defined_symbs | get_defined_symbs(r.lhs) | get_defined_symbs(r.rhs)
        constr_symbs = constr_symbs | get_constr_symbs(r.lhs) | get_constr_symbs(r.rhs)
        variables = variables | get_variables(r.lhs) | get_variables(r.rhs)
    return defined_symbs, constr_symbs, variables


def get_defined_symbs(term):
    if isinstance(term.tid, IdF) and term.tid.arity > 0:
        ds = set()
        for a in term.args:
            ds = ds | {term.tid} | get_defined_symbs(a)
        return ds
    else:
        return set()


def get_constr_symbs(term):
    if isinstance(term.tid, IdF) and term.tid.arity > 0:
        cs = set()
        for a in term.args:
            cs = cs | get_constr_symbs(a)
        return cs
    elif isinstance(term.tid, IdG):
        return {term.tid}
    else:
        return set()


def get_variables(term):
    if isinstance(term.tid, IdF) and term.tid.arity > 0:
        vs = set()
        for a in term.args:
            vs = vs | get_variables(a)
        return vs
    elif isinstance(term.tid, IdV):
        return {term.tid}
    else:
        return set()


def generate_defined_symb(max_arity):
    global names_defined_symbs
    random.seed()
    ar = random.randint(1, max_arity)
    (name, n) = random.choice(list(names_defined_symbs.items()))
    names_defined_symbs[name] = n + 1
    # real_name = ""
    if n == 0:
        real_name = name
    else:
        real_name = "{}{}".format(name, n)
    return IdF(real_name, ar)


def generate_constructor_symb():
    global names_constructor_symbs
    random.seed()
    (name, n) = random.choice(list(names_constructor_symbs.items()))
    names_constructor_symbs[name] = n + 1
    if n == 0:
        real_name = name
    else:
        real_name = "{}{}".format(name, n)
    return IdG(real_name)


def generate_var():
    global names_vars
    random.seed()
    (name, n) = random.choice(list(names_vars.items()))
    names_vars[name] = n + 1
    if n == 0:
        real_name = name
    else:
        real_name = "{}{}".format(name, n)
    return IdV(real_name)


def generate_rule(def_symbs, const_symbs, variables):
    random.seed()
    mult = 10
    lambd = 8
    (depth1, depth2) = (int(mult * random.expovariate(lambd)), int(mult * random.expovariate(lambd)))
    lhs = create_funct_term(def_symbs, const_symbs, variables, depth1)
    lhs_vars = list(get_variables(lhs))
    # Only lhs variables are considered as we cannot have new ones in the rhs
    rhs = create_funct_term(def_symbs, const_symbs, lhs_vars, depth2)
    return Rule(lhs, rhs)


def create_funct_term(def_symbs, const_symbs, variables, depth):
    random.seed()
    if depth > 0:
        tid = random.choice(def_symbs)
        where_def = [True] + random.choices([True, False], k=tid.arity - 1)
        random.shuffle(where_def)
        return Term(tid, [create_term(where_def[i], def_symbs, const_symbs + variables, depth - 1)
                          for i in range(tid.arity)])
    else:
        tid = random.choice(const_symbs)
        return Term(tid)


def create_term(must_be_def, def_symbs, no_ar_ids, depth):
    random.seed()
    if depth > 0 and must_be_def:
        tid = random.choice(def_symbs)
        where_def = [True] + random.choices([True, False], k=tid.arity - 1)
        random.shuffle(where_def)
        return Term(tid, [create_term(where_def[a], def_symbs, no_ar_ids, depth - 1)
                          for a in range(tid.arity)])
    else:
        tid = random.choice(no_ar_ids)
        return Term(tid)


def generate_trs(max_function_symbs=10, max_vars=3, max_rules=10, max_arity=3):
    random.seed()
    n_function_symbs = random.randint(1, max_function_symbs)
    n_defined_symbs = random.randint(1, n_function_symbs)
    n_constructor_symbs = 1 + n_function_symbs - n_defined_symbs
    n_vars = random.randint(0, max_vars)
    n_rules = random.randint(1, max_rules)
    defined_symbs = [generate_defined_symb(max_arity) for a in range(n_defined_symbs)]
    constructor_symbs = [generate_constructor_symb() for a in range(n_constructor_symbs)]
    variables = [generate_var() for a in range(n_vars)]
    rules = [generate_rule(defined_symbs, constructor_symbs, variables) for a in range(n_rules)]
    (defined_symbs_used, constructor_symbs_used, variables_used) = symbs_used(rules)
    return TRS(defined_symbs_used, constructor_symbs_used, variables_used, rules)


HELP_MESSAGE = "trs_gen\n" \
               "\t-h\t\t--help\t\t\tShow usage info\n" \
               "\t-g\t\t--ground\t\tGround TRS\n" \
               "\t-t\t\t--type TYPE\t\tSet rew sys type (CS-TRS)\n" \
               "\t-d DIR_PATH\t--dir DIR_PATH\t\tSet directory to write files\n" \
               "\t-r REP\t\t--repetitions REP\tSet repetitions\n" \
               "\tPYTHON3.8 REQUIRED!"

FILE_NAME = "gen"
FILE_N = 1


if __name__ == '__main__':
    MAX_DEFINED_SYMBS = 10
    MAX_VARS = 3
    MAX_RULES = 10
    MAX_ARITY = 3
    ground = False
    cstrs = False
    directory = ""
    rew_sys_type = "trs"
    repetitions = 1
    if len(sys.argv) == 0:
        print(HELP_MESSAGE)
        exit(0)
    elif '-h' in sys.argv or '--help' in sys.argv:
        print(HELP_MESSAGE)
        exit(0)
    else:
        for i in range(len(sys.argv)):
            if sys.argv[i] == '-g' or sys.argv[i] == '--ground':
                ground = True
            if sys.argv[i] == '-t' or sys.argv[i] == '--type':
                if i + 1 <= len(sys.argv) and sys.argv[i + 1] == 'cstrs':
                    cstrs = True
                    rew_sys_type = "cstrs"
            if sys.argv[i] == '-d' or sys.argv[i] == '--dir':
                if i + 1 <= len(sys.argv):
                    directory = sys.argv[i + 1]
                for j in range(len(sys.argv)):
                    if sys.argv[j] == '-r' or sys.argv[j] == '--repetitions':
                        if j + 1 <= len(sys.argv):
                            repetitions = int(sys.argv[j + 1])
    if repetitions < 1:
        repetitions = 1
    if ground:
        rew_sys_type += "ground"

    if directory != "":
        try:
            os.mkdir(directory)
            print("{} directory created".format(directory))
        except OSError:
            print("Creation of the directory %s failed" % directory)
        finally:
            os.chdir(directory)
            print("Switch to {} directory".format(directory))

    for i in range(repetitions):
        if ground:
            trs = generate_trs(MAX_DEFINED_SYMBS, 0, MAX_RULES, MAX_ARITY)
        else:
            trs = generate_trs(MAX_DEFINED_SYMBS, MAX_VARS, MAX_RULES, MAX_ARITY)

        initialize_names()

        if cstrs:
            trs.to_rand_cstrs()

        if directory != "":
            path = str(FILE_N) + "_" + FILE_NAME + "_" + rew_sys_type + ".trs"
            FILE_N += 1
            with open(path, 'w') as file:
                file.write(trs.to_str())
                print("{} created!".format(path))
        else:
            print(trs.to_str())
