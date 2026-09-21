from common_classes import *

attributes = {}
HIGHEST_IMPORTANCE = 11 # 1 above the highest defined precedence
OP_MAP = {  # Use https://docs.python.org/3/reference/expressions.html#operator-precedence for reference
            # TOKEN TYPE |      SYMBOL     | INFIX PREC,LEFT-ASS |  PREFIX PREC   | POSTFIX PREC | DISTFIX (closed) PREC
            'LBRACKET':   Operator("[",                                                           distfix=("]", 13, True, "INDEXACCESS")),
            'FIELDACCESS':Operator("'s ",    infix=(13,True)),
            'PERCENT':    Operator('%',                                             postfix=11),
            'FACTORIAL':  Operator('!',                                             postfix=11),
            'EXPONENT':   Operator('^',      infix=(10, True)),
            'MULTIPLY':   Operator('*',      infix=(8, True)),
            'MODULO':     Operator('mod',    infix=(8, True)),
            'INT_DIV':    Operator('div',    infix=(8, True)),
            'DIVIDE':     Operator('/',      infix=(8, True)),
            'PERCENTOF':  Operator('% of ',  infix=(8, True)),
            'PLUS':       Operator('+',      infix=(7, True)),
            'MINUS':      Operator('-',      infix=(7, True) ,        prefix=9),
            'INTO':       Operator('into',   infix=(7, True)),
            'FROMTO':     Operator('...',    infix=(6, True)),
            'INEQUALS':   Operator('!=',     infix=(5, True)),
            'IN':         Operator('in',     infix=(5, True)),
            'EQUALS':     Operator('equals', infix=(5, True)),
            'GETHAN':     Operator('>=',     infix=(5, True)),
            'LETHAN':     Operator('<=',     infix=(5, True)),
            'GREATERTHAN':Operator('>',      infix=(5, True)),
            'LESSTHAN':   Operator('<',      infix=(5, True)),
            'NOT':        Operator('not',                             prefix=4),
            'NAND':       Operator('nand',   infix=(3, True)),
            'AND':        Operator('and',    infix=(3, True)),
            'XOR':        Operator('xor',    infix=(2, True)),
            'NOR':        Operator('nor',    infix=(1, True)),
            'OR':         Operator('or',     infix=(1, True)),
            'GETTYPE':    Operator("typeOf",                          prefix=0),
            'PRINT':      Operator('print',                           prefix=0),
            'ASSIGN':     Operator('=',      infix=(0, True)),
        }

class Parser:
    def __init__(self, tokens: List[Token], import_map: dict):
        self.tokens = tokens
        self.pos = 0
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.theorems: Dict[str, TheoremDefinition] = {}
        self.import_map: dict = import_map
        self.operations = {}
        self.types = ['Type']
        self.pending_attributes = {}
        self.last_precolon = None

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def next(self) -> Token:
        return self.tokens[self.pos+1] if self.pos+1 < len(self.tokens) else self.tokens[-1]

    def advance(self):
        self.pos += 1

    def regress(self):
        self.pos -= 1

    def parse(self) -> tuple[Dict[str, AxiomDefinition], Dict[str, TheoremDefinition], Optional[list], List[Statement], list, list]:
        hypothesis = []
        hypothesis_to_append = []
        proofs = []
        ordered : List[tuple[str, FunctionDefinition|tuple]] = [('type', (FunctionDefinition(name='Type', args=[], return_type='Type', attributes={}, body=[]), False))]

        hypothesis_to_append.append(Statement('let', [('VARIABLE', 'Type')], value=('Type', 'Type'), line=self.current().line_num))
        hypothesis_to_append.append(Statement('typehint', ['Type', 'Type'], line=self.current().line_num))

        while self.current().type != 'EOF':
            if self.current().type == 'AXIOM':
                axiom = self.parse_axiom()
                self.axioms[axiom.name] = axiom
                ordered.append(('axiom', axiom))
            elif self.current().type == 'THEOREM':
                theorem = self.parse_theorem()
                self.theorems[theorem.name] = theorem
                ordered.append(('theorem', theorem))

            elif self.current().type == 'AT':
                self.advance()  # @
                self.advance()  # [
                attr_name = self.current().value
                self.advance()
                attr_args = []
                while self.current().type != 'RBRACKET':
                    attr_args.append(self.current().value)
                    self.advance()
                self.advance()  # ]
                self.pending_attributes[attr_name] = attr_args


            elif self.current().type == 'OPERATION':
                op = self.parse_operation_definition()
                if op.left_type is None:
                    if op.operator not in OP_MAP:
                        OP_MAP[op.operator] = Operator(op.operator, prefix=HIGHEST_IMPORTANCE)
                else:
                    if op.operator not in OP_MAP:
                        OP_MAP[op.operator] = Operator(op.operator, infix=(HIGHEST_IMPORTANCE, True))
                ordered.append(('operation', op))

            elif self.current().type == 'FUNCTION':
                funct = self.parse_function()
                ordered.append(('function', funct))

            elif self.current().type == 'TYPE':
                td, is_record = self.parse_type()
                self.types.append(td.name)
                hypothesis_to_append.append(Statement('let', [('VARIABLE', td.name)], value=('Type', td.name), line=self.current().line_num))
                hypothesis_to_append.append(Statement('typehint', [td.name, 'Type'], line=self.current().line_num))
                ordered.append(('type', (td, is_record)))
            elif self.current().type == 'IMPORT':
                self.advance()
                if self.current().type == 'VARIABLE':
                    return self.axioms, self.theorems, hypothesis, proofs, [self.current().value, self.current().line_num], ordered
            elif self.current().type == 'HYPOTHESIS':
                self.advance()
                if self.current().type == 'COLON':
                    self.advance()
                self.advance()
                hypothesis.extend(hypothesis_to_append)
                hypothesis.extend(self.parse_block())
            else:
                stmt = self.parse_statement()
                if stmt:
                    proofs.extend(stmt)
        return self.axioms, self.theorems, hypothesis, proofs, [], ordered

    def parse_named_block(self, block_keyword):
        line = self.current().line_num
        if self.current().type != block_keyword:
            print_error(line, f"Syntax Error: Expected '{block_keyword}'", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{block_keyword}'", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{block_keyword}'", self.import_map)
            sys.exit(1)
        self.advance()
        statements = []
        while self.current().type != 'DEDENT':
            statements.extend(self.parse_statement())
        self.advance()
        return statements

    def extract_lets(self, statements):
        let_objects = []
        let_numvars = []
        for stmt in statements:
            if stmt.type == 'let':
                let_objects.append(stmt.objects[0])
            elif stmt.type == 'let_numvar':
                let_numvars.append(stmt.objects[0])
        return let_objects, let_numvars

    def parse_axiom(self) -> AxiomDefinition:
        self.advance()  # skip 'axiom'
        line = self.current().line_num

        if self.current().type != 'VARIABLE':
            print_error(line, "Syntax Error: Expected axiom name", self.import_map)
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after axiom name", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, "Syntax Error: Expected indented block after axiom name", self.import_map)
            sys.exit(1)
        self.advance()

        given_statements = self.parse_named_block('GIVEN')
        then_statements = self.parse_named_block('THEN')

        let_objects, let_numvars = self.extract_lets(given_statements)

        return AxiomDefinition(name, given_statements, then_statements, let_objects, let_numvars)

    def parse_theorem(self) -> TheoremDefinition:
        self.advance()  # skip 'theorem'
        line = self.current().line_num

        if self.current().type != 'VARIABLE':
            print_error(line, "Syntax Error: Expected theorem name", self.import_map)
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after theorem name", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, "Syntax Error: Expected indented block after theorem name", self.import_map)
            sys.exit(1)
        self.advance()

        given_statements = self.parse_named_block('GIVEN')
        then_statements = self.parse_named_block('THEN')
        proof_statements = self.parse_named_block('PROOF')

        let_objects, let_numvars = self.extract_lets(given_statements)

        return TheoremDefinition(name, given_statements, then_statements, proof_statements, let_objects, let_numvars)

    def parse_sum_operands(self, first_operand: str, allowed_types: Sequence[str]) -> List[tuple]:
        """Returns list of (sign, name) pairs. First operand always gets '+'."""
        operands = [('+', first_operand)]
        while self.current().type in ('PLUS', 'MINUS'):
            sign = '+' if self.current().type == 'PLUS' else '-'
            self.advance()
            if self.current().type not in allowed_types:
                line = self.current().line_num
                print_error(line, f"Syntax Error: Expected {allowed_types} after '+'/'-'", self.import_map)
                sys.exit(1)
            operands.append((sign, self.current().value))
            self.advance()
        return operands

    def parse_axiom_bindings(self) -> list:
        raw_args = []
        while self.current().type != 'RBRACE':
            expr = self.expr()
            raw_args.append(expr)
            if self.current().type == 'COMMA':
                self.advance()
        return raw_args

    def _parse_equality_chain(self, first_operands, left_type, line):
        """Parse = B = C = D... and return list of all sides."""
        sides = [first_operands]
        while self.current().type == 'ASSIGN':
            self.advance()
            rhs = self.parse_rhs(left_type, line)
            if rhs[0] == 'single':
                _, right, right_type = rhs
                sides.append((right, right_type))
            else:
                _, right_operands = rhs
                sides.append(right_operands)
        return sides

    def parse_operation_definition(self):
        self.advance()  # skip 'operation'

        first = self.current()
        self.advance()
        specialization = None

        second = self.current()
        self.advance()

        if first.value in self.types:
            left_type = first.value
            operator = second.type if second.type in OP_MAP else second.value
            if self.current().type == 'ARROW_TYPE':
                right_type = None
            else:
                right_type = self.current().value
                self.advance()
                specialization = None
                if self.current().type == 'SEMICOLON':
                    self.advance()
                    specialization = self.current().value
                    self.advance()
        else:
            left_type = None
            operator = first.type if first.type in OP_MAP else first.value
            right_type = second.value
            specialization = None

        return_type = None
        if self.current().type == 'ARROW_TYPE':
            self.advance()
            return_type = self.current().value
            self.advance()

        if left_type is None:
            if operator not in OP_MAP:
                OP_MAP[operator] = Operator(operator, prefix=HIGHEST_IMPORTANCE)
        else:
            if operator not in OP_MAP:
                OP_MAP[operator] = Operator(operator, infix=(HIGHEST_IMPORTANCE, True))

        body = []
        witnesses = []
        self.advance()  # skip colon or newline
        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                if self.current().type == 'WITNESS':
                    if return_type != "Bool":
                        print_error(self.current().line_num, f"Witnesses are only allowed in operations with a Bool return type. Found: {return_type}", self.import_map)
                    self.advance()
                    var_name = self.current().value
                    self.advance()
                    if self.current().type == 'BE':
                        self.advance()
                        var_type = self.current().value
                        self.advance()
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('inductive', var_name, var_type, expr))
                    elif self.current().type == 'EQUALS' or self.current().type == 'ASSIGN':
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('base', var_name, expr))
                else:
                    case = self.parse_statement()
                    body.extend(case)
            self.advance()

        attributes = self.pending_attributes
        self.pending_attributes = {}

        if specialization is not None:
            attributes['specialized_type'] = specialization

        o = OperationDefinition(
            left_type=left_type,
            operator=operator,
            right_type=right_type,
            return_type=return_type,
            body=body,
            witnesses=witnesses,
            attributes=attributes,
        )
        return o

    def parse_function(self):
        self.advance()  # skip 'function'

        first = self.current()
        self.advance()

        name = first.value
        args=[]

        if self.current().type != 'LPAR':
            print_error(self.current().line_num,
                        f"Expected parentheses after function definition. Found: {self.current().value}", self.import_map)

        self.advance()
        saw_default = False
        while self.current().type == 'VARIABLE':
            arg_name = self.current().value
            self.advance()
            default = None
            if self.current().type == 'ASSIGN':
                self.advance()
                default = self.expr()
                saw_default = True
            elif saw_default:
                print_error(self.current().line_num,
                            "Required parameters cannot follow parameters with defaults", self.import_map)
            args.append((arg_name, default))
            if self.current().type != 'COMMA':
                break
            self.advance()

        if self.current().type != 'RPAR':
            print_error(self.current().line_num,
                        f"Expected closing parentheses after function definition. Found: {self.current().value}",
                        self.import_map)
        self.advance()
        if self.current().type != 'COLON':
            print_error(self.current().line_num,
                        f"Expected colon after function definition. Found: {self.current().value}", self.import_map)
        self.advance()
        return_type = None
        if self.current().type == 'ARROW_TYPE':
            self.advance()
            return_type = self.current().value
            self.advance()


        body = []
        witnesses = []
        self.advance()
        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                if self.current().type == 'WITNESS':
                    if return_type != "Bool":
                        print_error(self.current().line_num, f"Witnesses are only allowed in operations with a Bool return type. Found: {return_type}", self.import_map)
                    self.advance()
                    var_name = self.current().value
                    self.advance()
                    if self.current().type == 'BE':
                        self.advance()
                        var_type = self.current().value
                        self.advance()
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('inductive', var_name, var_type, expr))
                    elif self.current().type == 'EQUALS' or self.current().type == 'ASSIGN':
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('base', var_name, expr))
                else:
                    case = self.parse_statement()
                    body.extend(case)
            self.advance()

        attributes = self.pending_attributes
        self.pending_attributes = {}

        o = FunctionDefinition(
            name=name,
            args=args,
            return_type=return_type,
            body=body,
            attributes=attributes,
        )
        return o

    def parse_type(self):
        self.advance()  # skip 'type'

        first = self.current()
        is_record = False
        self.advance()
        name = first.value
        args=[]

        if self.current().type != 'LPAR':
            print_error(self.current().line_num,
                        f"Expected parentheses after type definition. Found: {self.current().value}", self.import_map)

        self.advance()
        saw_default = False
        while self.current().type == 'VARIABLE':
            arg_name = self.current().value
            self.advance()
            default = None
            if self.current().type == 'ASSIGN':
                self.advance()
                default = self.expr()
                saw_default = True
            elif saw_default:
                print_error(self.current().line_num,
                            "Required parameters cannot follow parameters with defaults", self.import_map)
            args.append((arg_name, default))
            if self.current().type != 'COMMA':
                break
            self.advance()
        if self.current().type != 'RPAR':
            print_error(self.current().line_num,
                        f"Expected closing parentheses after type definition. Found: {self.current().value}",
                        self.import_map)
        self.advance()
        if self.current().type != 'COLON':
            print_error(self.current().line_num,
                        f"Expected colon after type definition. Found: {self.current().value}", self.import_map)
        self.advance()

        body = []
        witnesses = []
        self.advance()
        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                if self.current().type == 'RECORDTYPE':
                    is_record = True
                    self.advance()  # skip 'recordType'
                    if self.current().type == 'NEWLINE':
                        self.advance()
                    continue
                if self.current().type == 'WITNESS':
                    if name != "Bool":
                        print_error(self.current().line_num, f"Witnesses are only allowed in operations with a Bool return type. Found: {name}", self.import_map)
                    self.advance()
                    var_name = self.current().value
                    self.advance()
                    if self.current().type == 'BE':
                        self.advance()
                        var_type = self.current().value
                        self.advance()
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('inductive', var_name, var_type, expr))
                    elif self.current().type == 'EQUALS' or self.current().type == 'ASSIGN':
                        self.advance()
                        expr = self.expr()
                        witnesses.append(('base', var_name, expr))
                else:
                    case = self.parse_statement()
                    body.extend(case)
                if self.current().type != 'DEDENT':
                    self.advance()

        attributes = self.pending_attributes
        self.pending_attributes = {}

        o = FunctionDefinition(
            name=name,
            args=args,
            return_type=name,
            body=body,
            attributes=attributes,
        )
        return o, is_record

    def expr(self, prev_prec=-1):
        left = self.atom()
        while True:
            tok = self.current()
            op = tok.type if tok.type in OP_MAP else tok.value if tok.value in OP_MAP else None
            if op is None:
                if tok.type == 'VARIABLE':
                    op = tok.value
                    op_info = Operator(tok.value, infix=(HIGHEST_IMPORTANCE, True))
                else:
                    break
            else:
                op_info = OP_MAP[op]

            if op_info.postfix is not None:
                prec = op_info.postfix
                if prec <= prev_prec:
                    break
                self.advance()
                left = Expression(op, left, 'none_for_unary', witness=None, line=tok.line_num)
                continue

            if op_info.distfix is not None:
                closing, prec, left_assoc, new_op_name = op_info.distfix
                if prec <= prev_prec:
                    break
                self.advance()
                inner = self.expr(-1)
                if self.current().value != closing:
                    print_error(self.current().line_num, f"Expected '{closing}'", self.import_map)
                    sys.exit(1)
                self.advance()
                left = Expression(new_op_name, left, inner, witness=None, line=self.current().line_num)
                continue

            if op_info.infix is None or op_info.infix[0] <= prev_prec:
                break
            prec, left_assoc = op_info.infix
            self.advance()
            left = Expression(op, left, self.expr(prec if left_assoc else prec - 1), witness=None, line=self.current().line_num)
        if self.current().type == 'WITH_WITNESS':
            WITH_WITNESS_PREC = -1
            if prev_prec > WITH_WITNESS_PREC:
                return left
            if not isinstance(left, Expression):
                print_error(self.current().line_num,
                            "'with witness' must follow an operation",
                            self.import_map)
                sys.exit(1)
            self.advance()
            witness = self.expr()
            left.witness = witness
        return left

    def atom(self):
        tok = self.current()
        val_type = tok.type
        value = tok.value

        if val_type.startswith('LIT'):
            self.advance()
            return val_type, value


        elif val_type == 'IDENT':
            self.advance()
            return 'VARIABLE', value

        elif val_type == 'ANGLE':
            self.advance()
            return 'VARIABLE', value

        elif val_type in OP_MAP and OP_MAP[val_type].prefix is not None:
            self.advance()
            return Expression(val_type, self.expr(OP_MAP[val_type].prefix), 'none_for_unary', witness=None, line=self.current().line_num)

        elif value in OP_MAP and OP_MAP[value].prefix is not None:
            self.advance()
            return Expression(value, self.expr(OP_MAP[value].prefix), 'none_for_unary', witness=None, line=self.current().line_num)


        elif val_type == 'VARIABLE':
            self.advance()
            # check for function call
            if self.current().type == 'LPAR':
                self.advance()
                call_args = []
                if self.current().type != 'RPAR':
                    call_args.append(self.expr(-1))
                    while self.current().type == 'COMMA':
                        self.advance()
                        call_args.append(self.expr(-1))
                if self.current().type != 'RPAR':
                    print_error(tok.line_num, f"Expected closing ')', found '{self.current().value}'", self.import_map)
                    sys.exit(1)
                self.advance()
                return Expression('CALL', ('VARIABLE', value), call_args, witness=None, line=tok.line_num)
            return 'VARIABLE', value

        elif val_type == 'LPAR':
            self.advance()
            first = self.expr(-1)
            if self.current().type == 'COMMA':
                elements = [first]
                while self.current().type == 'COMMA':
                    self.advance()
                    if self.current().type == 'RPAR':
                        break
                    elements.append(self.expr(-1))
                if self.current().type != 'RPAR':
                    print_error(tok.line_num, "Expected closing ')'", self.import_map)
                    sys.exit(1)
                self.advance()
                if all(isinstance(e, Expression) and e.operator == 'ASSIGN' for e in elements):
                    return 'NAMEDTUPLE', elements
                return 'TUPLE', elements
            else:
                if self.current().type != 'RPAR':
                    print_error(tok.line_num, f"Expected closing ')', found '{self.current().value}'", self.import_map)
                    sys.exit(1)
                self.advance()
                if isinstance(first, Expression) and first.operator == 'ASSIGN':
                    return 'NAMEDTUPLE', [first]
                return first
        else:
            print_error(tok.line_num, f"Expected operand, got {val_type}", self.import_map)
            sys.exit(1)

    def parse_block(self):
        statements = []
        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                stmt = self.parse_statement()
                statements.extend(stmt)
            self.advance()  # skip DEDENT
        return statements

    def parse_statement(self) -> List[Statement]:
        statements = []
        line = self.current().line_num

        if self.current().type == 'VARIABLE' and self.pos + 1 < len(self.tokens) and self.tokens[
            self.pos + 1].type == 'LBRACE':
            axiom_name = self.current().value
            self.advance()
            self.advance()

            raw_args = self.parse_axiom_bindings()

            if self.current().type != 'RBRACE':
                print(f"Syntax Error: Expected '}}' after axiom bindings")
                sys.exit(1)
            self.advance()
            if self.current().type == 'CONCL_ARROW':
                self.advance()
                conclusion = self.parse_statement()
                statements.append(Statement('axiom_application', [axiom_name], value=raw_args, line=line))
                statements.extend(conclusion)
            return statements

        elif self.current().type == 'LET':
            self.advance()
            name_type = self.current().type
            name = self.current().value
            left_expr = self.expr()
            type_annotation = None

            if self.current().type in ('COLON', 'BE'):
                self.advance()
                type_annotation = self.current().value
                self.advance()
            if self.current().type == 'ASSIGN':
                self.advance()
                value = self.expr()
                s = Statement('let', [left_expr], value=value, line=line)
                statements.append(s)
            elif type(left_expr) is Expression and left_expr.operator == 'ASSIGN':
                s = Statement('let', [left_expr.left], value=left_expr.right, line=line)
                statements.append(s)

            if type_annotation is not None:
                hint_target = left_expr if isinstance(left_expr, Expression) else name
                statements.append(Statement('typehint', [hint_target, type_annotation], line=line))
            value = None
            if name_type == 'IDENT':
                if self.current().type == 'ASSIGN':
                    self.advance()
                    value = self.expr()
                elif self.current().type == 'ISO':
                    self.advance()
                    l = self.current().line
                    base = None
                    if self.current().type == 'BASE':
                        self.advance()
                        base = self.current().value
                        self.advance()
                    points = name
                    if base is None:

                        side1 = points[0] + points[2]
                        side2 = points[1] + points[2]
                    else:
                        non_base = [p for p in points if p not in base]
                        side1 = base[0] + non_base[0]
                        side2 = base[1] + non_base[0]

                    expr = Expression(
                        operator='ASSIGN',
                        left=('VARIABLE', side1),
                        right=('VARIABLE', side2),
                        line=line
                    )
                    statements.append(Statement('let', [('IDENT', side1)], value=None, line=line))
                    statements.append(Statement('let', [('IDENT', side2)], value=None, line=line))
                    s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                    statements.append(s)
                    self.advance()
                statements.append(Statement('let', [(name_type, name)], value=value, line=line))
            elif name_type == 'ANGLE':
                if self.current().type == 'ASSIGN':
                    self.advance()
                    value = self.expr()
                statements.append(Statement('let', [(name_type, name)], value=value, line=line))

        elif self.current().type == 'IF':
            self.advance()
            condition = self.expr()
            self.advance()  # skip newline
            then_block = self.parse_block()
            else_block = []
            if self.current().type == 'ELSE':
                self.advance()
                self.advance()
                else_block = self.parse_block()
            statements.append(Statement('if', [condition, then_block, else_block]))


        elif self.current().type == 'VARIABLE':

            if self.current().value not in OP_MAP:

                expr = self.expr()  # parse the full lvalue: e's n, t[0], x, whatever

                type_annotation = None

                value = None

                if self.current().type in ('BE', 'COLON'):
                    self.advance()

                    type_annotation = self.current().value

                    self.advance()

                if self.current().type == 'ASSIGN':
                    self.advance()

                    value = self.expr()

                if type_annotation is not None or value is not None:

                    # it was a declaration/assignment

                    s = Statement('let', [expr], value=value, line=line)

                    statements.append(s)

                    if type_annotation:
                        statements.append(Statement('typehint', [expr, type_annotation], line=line))

                else:

                    # it was a plain expression statement

                    self.regress()

                    l = self.current().line

                    self.advance()

                    s = Statement('expression', [expr, l.strip()], line=self.current().line_num)

                    statements.append(s)

            else:

                # OP_MAP case, unchanged

                expr = self.expr()

                self.regress()

                l = self.current().line

                self.advance()

                s = Statement('expression', [expr, l.strip()], line=self.current().line_num)

                statements.append(s)

        elif self.current().type in OP_MAP or self.current().type == 'LPAR':
            expr = self.expr()
            self.regress()
            l = self.current().line
            self.advance()
            s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
            statements.append(s)

        elif self.current().type == 'IDENT':
            name = self.current().value
            if self.current().value not in OP_MAP:
                self.regress()
                if self.current().type in ('COLON','BE'): #this is a type
                    self.advance() # var (self)
                    make_operation = False
                else:
                    self.advance()
                    make_operation = True

                if make_operation:
                    expr = self.expr()
                    self.regress()
                    l = self.current().line
                    self.advance()
                    s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                    statements.append(s)
            else:
                expr = self.expr()
                self.regress()
                l = self.current().line
                self.advance()
                s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                statements.append(s)

            if self.current().type == 'ISO':
                self.advance()
                l = self.current().line
                base = None
                if self.current().type == 'BASE':
                    self.advance()
                    base = self.current().value
                    self.advance()
                points = name
                if base is None:

                    side1 = points[0] + points[2]
                    side2 = points[1] + points[2]
                else:
                    non_base = [p for p in points if p not in base]
                    side1 = base[0] + non_base[0]
                    side2 = base[1] + non_base[0]

                expr = Expression(
                    operator='ASSIGN',
                    left=('VARIABLE', side1),
                    right=('VARIABLE', side2),
                    line=line
                )
                statements.append(Statement('let', [('IDENT', side1)], value=None, line=line))
                statements.append(Statement('let', [('IDENT', side2)], value=None, line=line))
                s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                statements.append(s)
                self.advance()

        elif self.current().type == 'ANGLE':
            expr = self.expr()
            self.regress()
            l = self.current().line
            self.advance()
            s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
            statements.append(s)

        elif self.current().type.startswith('LIT'):
            l = self.current().line
            expr = self.expr()
            s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
            statements.append(s)
            self.advance()

        elif self.current().type == 'GIVES':
            self.advance()
            l = self.current().line
            expr = self.expr()
            s = Statement('gives', [expr, l.strip()], line=line)
            statements.append(s)

        elif self.current().type == 'ERROR':
            self.advance()
            l = self.current().line
            expr = ('LITSTR', "")
            if self.current().type in ('VARIABLE', 'LPAR', 'IDENT', 'ANGLE') or self.current().type.startswith('LIT'):
                expr = self.expr()
            s = Statement('error', [expr, l.strip()], line=line)
            statements.append(s)

        else:
            self.advance()
        while self.current().type == 'EQUALS':
            self.advance()
            if self.current().type == 'LITBOOL':
                goal = self.current().value == 'true'
                self.advance()
                for s in statements:
                    if not goal:
                        s.goal = not s.goal

        if self.current().type == 'NEWLINE':
            self.advance()

        return statements

    def parse_rhs(self, allowed_types: Sequence[str], line: int) -> tuple:
        if self.current().type not in  ('LITINT', 'NUMVAR', 'LITNAT', 'LITFLOAT') and self.current().type not in allowed_types:
            print_error(line, f"Syntax Error: Unexpected token '{self.current().value}' after '='",
                        self.import_map)
            sys.exit(1)

        first_val = self.current().value
        first_type = self.current().type
        self.advance()

        if first_type == 'NUMBER' and self.current().type in ('PLUS', 'MINUS'):
            operands = [('+', first_val)]
            while self.current().type in ('PLUS', 'MINUS'):
                sign = '+' if self.current().type == 'PLUS' else '-'
                self.advance()
                if self.current().type not in allowed_types and self.current().type not in ('NUMBER', 'NUMVAR'):
                    print_error(line, f"Syntax Error: Expected {allowed_types}, number, or numvar after '+'/'-'",
                                self.import_map)
                    sys.exit(1)
                operands.append((sign, self.current().value))
                self.advance()
            return ('sum', operands)

        if first_type not in ('NUMBER', 'NUMVAR') and self.current().type in ('PLUS', 'MINUS'):
            rhs_operands = self.parse_sum_operands(first_val, allowed_types)
            return ('sum', rhs_operands)

        return ('single', first_val, first_type)