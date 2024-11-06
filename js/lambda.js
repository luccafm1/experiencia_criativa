let globalDefinitions = {
    'Y': 'λf.(λx.(f (x x))) (λx.(f (x x)))',

    'succ': 'λn.λf.λx.(f ((n f) x))',
    'add': 'λm.λn.λf.λx.((m f) ((n f) x))',
    'sub': 'λm.λn.(n pred m)',
    'mult': 'λm.λn.λf.(m (n f))',
    'pred': 'λn.λf.λx.((n (λg.λh.(h (g f)))) (λu.x) (λu.u))',

    'true': 'λx.λy.x',
    'false': 'λx.λy.y',
    'and': 'λp.λq.((p q) p)',
    'or': 'λp.λq.((p p) q)',
    'not': 'λp.λa.λb.((p b) a)',
    'if': 'λp.λa.λb.((p a) b)',
    'isnil': 'λlst.(lst (λx.false) true)',
    'iszero': 'λn.(n (λx.false) true)',

    'fact': 'Y (λf.λn.(if (iszero n) 1 (mult n (f (pred n)))))',

    'cons': 'λx.λy.λf.((f x) y)',
    'car': 'λp.(p (λx.λy.x))',
    'cdr': 'λp.(p (λx.λy.y))',
    'nil': 'λc.λn.n',
} 

function listDefinitions() {
    const outputDiv = document.getElementById('definitions');  
    let content = `<div class='globals'>`;
        
    for (const [key, value] of Object.entries(globalDefinitions)) {
        content += `<div class='definition'>
                        <div class='key-definition'><strong>${key}</strong></div> <div class='value-definition'>${value}</div>
                    </div>`;
    }
    content += `</div>
                <textarea id="global-input" style="overflow:hidden" class="global-input" placeholder="Enter new definition or replace an existing one (e.g., 'add = λm.λn.λf.λx.((m f) ((n f) x))')"></textarea>
                <button id="add-definition-button">Add Definition</button>`;
    
    outputDiv.innerHTML = content;
    
    document.getElementById('add-definition-button').addEventListener('click', addDefinition);

    const textarea = document.getElementById('global-input');
    textarea.addEventListener("input", () => {
        const cursorPosition = textarea.selectionStart;
        const beforeCursor = textarea.value.slice(0, cursorPosition);
        const afterCursor = textarea.value.slice(cursorPosition);

        const updatedBeforeCursor = beforeCursor.replace(/\blambda\b|\\/g, 'λ');
        const updatedText = updatedBeforeCursor + afterCursor;

        const adjustment = beforeCursor.length - updatedBeforeCursor.length;

        if (updatedText !== textarea.value) {
            textarea.value = updatedText;
            textarea.setSelectionRange(cursorPosition - adjustment, cursorPosition - adjustment);
        }
    });
}

function addDefinition() {
    const input = document.getElementById('global-input').value.trim();
    const [name, expr] = input.split('=').map(part => part.trim());

    if (!name || !expr) {
        alert('Please enter a valid definition in the format: name = λexpression');
        return;
    }

    globalDefinitions[name] = expr;

    document.getElementById('global-input').value = '';
    listDefinitions();
}

window.onload = listDefinitions;

class Term {
    toString() {
        throw new Error("Abstract method");
    }
}

class Variable extends Term {
    constructor(name) {
        super();
        this.name = name;
    }

    toString() {
        return this.name;
    }
}

class Expression extends Term {
    constructor(variable, body) {
        super();
        this.variable = variable;
        this.body = body;
    }

    toString() {
        return `λ${this.variable}.${this.body}`;
    }
}

class Application extends Term {
    constructor(func, argument) {
        super();
        this.function = func;
        this.argument = argument;
    }

    toString() {
        const funcStr = this.function instanceof Expression ? 
            `(${this.function})` : this.function.toString();
        const argStr = (this.argument instanceof Application || 
            this.argument instanceof Expression) ? 
            `(${this.argument})` : this.argument.toString();
        return `${funcStr} ${argStr}`;
    }
}

function tokenize(str) {
    const tokens = [];
    let i = 0;
    
    while (i < str.length) {
        const c = str[i];
        if (c === 'λ' || c === '.' || c === '(' || c === ')') {
            tokens.push({ type: 'symbol', value: c });
            i++;
        } else if (/\s/.test(c)) {
            i++;
        } else if (/\d/.test(c)) {
            let num = '';
            while (i < str.length && /\d/.test(str[i])) {
                num += str[i];
                i++;
            }
            tokens.push({ type: 'number', value: num });
        } else if (/[a-zA-Z_+\-\/:*]/.test(c)) {
            let varName = '';
            while (i < str.length && /[a-zA-Z_+\-\/:*]/.test(str[i])) {
                varName += str[i];
                i++;
            }
            if (varName === 'true' || varName === 'false') {
                tokens.push({ type: 'boolean', value: varName });
            } else {
                tokens.push({ type: 'variable', value: varName });
            }
        } else {
            throw new Error(`Unexpected character '${c}' at position ${i}`);
        }
    }
    return tokens;
}


class Parser {
    constructor(tokens) {
        this.tokens = tokens;
        this.pos = 0;
    }

    peek() {
        return this.tokens[this.pos] || null;
    }

    consume() {
        return this.tokens[this.pos++] || null;
    }

    parse() {
        const term = this.parseExpression();
        if (this.pos < this.tokens.length) {
            throw new Error("Unexpected tokens at the end");
        }
        return term;
    }

    parseExpression() {
        const nextToken = this.peek();
        if (nextToken && nextToken.type === 'symbol' && nextToken.value === 'λ') {
            return this.parseAbstraction();
        } else {
            return this.parseApplication();
        }
    }

    parseAbstraction() {
        const lambdaToken = this.consume(); // consume 'λ'
        if (!lambdaToken || lambdaToken.type !== 'symbol' || lambdaToken.value !== 'λ') {
            throw new Error("Expected 'λ'");
        }
        const varToken = this.consume();
        if (!varToken || varToken.type !== 'variable') {
            throw new Error("Expected variable name after 'λ'");
        }
        const variable = new Variable(varToken.value);
        const dotToken = this.consume();
        if (!dotToken || dotToken.type !== 'symbol' || dotToken.value !== '.') {
            throw new Error("Expected '.' after variable name in abstraction");
        }
        const body = this.parseExpression();
        return new Expression(variable, body);
    }

    parseApplication() {
        let left = this.parseAtom();
        while (true) {
            const nextToken = this.peek();
            if (!nextToken || (nextToken.type === 'symbol' && ['λ', '.', ')'].includes(nextToken.value))) {
                break;
            }
            const right = this.parseAtom();
            left = new Application(left, right);
        }
        return left;
    }

    parseAtom() {
        const tokenObj = this.peek();
        if (!tokenObj) {
            throw new Error("Unexpected end of input");
        }
        const { type, value } = tokenObj;
        if (type === 'symbol' && value === '(') {
            this.consume();
            const term = this.parseExpression();
            const closing = this.consume();
            if (!closing || closing.type !== 'symbol' || closing.value !== ')') {
                throw new Error("Expected ')'");
            }
            return term;
        } else if (type === 'symbol' && value === 'λ') {
            return this.parseAbstraction();
        } else if (type === 'number') {
            this.consume();
            return numToChurchTerm(parseInt(value, 10));
        } else if (type === 'boolean') {
            this.consume();
            return booleanToLambdaTerm(value === 'true');
        } else if (type === 'variable') {
            this.consume();
            return new Variable(value);
        } else {
            throw new Error(`Unexpected token '${value}'`);
        }
    }
}


function freeVariables(term) {
    if (term instanceof Variable) {
        return new Set([term.name]);
    } else if (term instanceof Expression) {
        const bodyFv = freeVariables(term.body);
        bodyFv.delete(term.variable.name);
        return bodyFv;
    } else if (term instanceof Application) {
        const fv = freeVariables(term.function);
        freeVariables(term.argument).forEach(v => fv.add(v));
        return fv;
    }
    throw new Error("Unknown term type in free_variables");
}

function freshVariableName(){
    
}

let counter = 0;
function freshVariableName(base = 'x') {
    return `${base}${++counter}`;
}

function substitute(term, variable, replacement) {
    if (term instanceof Variable) {
        return term.name === variable.name ? replacement : term;
    } else if (term instanceof Expression) {
        if (term.variable.name === variable.name) {
            return term;
        } else if (freeVariables(replacement).has(term.variable.name)) {
            const newVarName = freshVariableName();
            const newVar = new Variable(newVarName);
            let newBody = substitute(term.body, term.variable, newVar);
            newBody = substitute(newBody, variable, replacement);
            return new Expression(newVar, newBody);
        } else {
            const newBody = substitute(term.body, variable, replacement);
            return new Expression(term.variable, newBody);
        }
    } else if (term instanceof Application) {
        const newFunc = substitute(term.function, variable, replacement);
        const newArg = substitute(term.argument, variable, replacement);
        return new Application(newFunc, newArg);
    }
    throw new Error("Unknown term type in substitution");
}

function parse(str) {
    const tokens = tokenize(str);
    const parser = new Parser(tokens);
    return parser.parse();
}

function expandSimpleSyntax(input) {
    const tokens = tokenize(input);
    const expandingTokens = new Set();

    function expandToken(tokenObj) {
        const { type, value } = tokenObj;
        if (type === 'variable' && globalDefinitions[value]) {
            if (expandingTokens.has(value)) {
                throw new Error(`Circular definition detected for token '${value}'`);
            }
            expandingTokens.add(value);
            let expandedDef = expandDefinition(globalDefinitions[value]);
            expandingTokens.delete(value);
            return expandedDef;
        } else {
            return value;
        }
    }

    function expandDefinition(definition) {
        const trimmedDef = definition.trim();
        const startsWithLambda = trimmedDef.startsWith('λ');

        const defTokens = tokenize(definition);
        const expanded = defTokens.map(expandToken).join(' ');

        return startsWithLambda ? `(${expanded})` : expanded;
    }

    const expandedTokens = tokens.map(expandToken);
    return expandedTokens.join(' ');
}




function showExpanded() {
    const input = document.getElementById('input').value;
    const outputDiv = document.getElementById('output');
    
    try {
        outputDiv.textContent = '';
        outputDiv.style.textAlign = 'center';
        const expanded = expandSimpleSyntax(input);
        outputDiv.textContent = expanded;
        outputDiv.style.display = 'block';
    } catch (error) {
        document.getElementById('error').textContent = `Error: ${error.message}`;
    }
}

function showSyntaxTree() {
    const input = document.getElementById('input').value;
    const outputDiv = document.getElementById('output');
    const errorDiv = document.getElementById('error');

    try {
        errorDiv.textContent = '';
        outputDiv.style.textAlign = 'left'; 

        const expressionToParse = expandSimpleSyntax(input);
        const term = parse(expressionToParse);
        const syntaxTree = getSyntaxTree(term);

        outputDiv.innerHTML = `${syntaxTree}`; 
    } catch (error) {
        errorDiv.textContent = `Error: ${error.message}`;
        outputDiv.textContent = '';
    }
}


function getSyntaxTree(term, indent = '', isLast = true) {
    let treeStructure = '';

    if (term instanceof Variable) {
        treeStructure += `${indent}${isLast ? '└── ' : '├── '}${term.name}\n`;
    } else if (term instanceof Expression) {
        treeStructure += `${indent}${isLast ? '└── ' : '├── '}λ${term.variable.name}\n`;
        treeStructure += getSyntaxTree(term.body, indent + (isLast ? '    ' : '│   '), true);  
    } else if (term instanceof Application) {
        treeStructure += `${indent}${isLast ? '└── ' : '├── '}@\n`;
        treeStructure += getSyntaxTree(term.function, indent + (isLast ? '    ' : '│   '), false); 
        treeStructure += getSyntaxTree(term.argument, indent + (isLast ? '    ' : '│   '), true); 
    }
    
    return treeStructure;
}


function evaluate(term, maxSteps=1000) {
    let previousTerm = null;
    let currentTerm = term;
    let step_count = 0;
    const steps = [];
    
    while (previousTerm === null || currentTerm.toString() !== previousTerm.toString()) {
        if (step_count >= maxSteps){
            return steps.slice(Math.max(steps.length-10, 0)).concat(["Infinite recursion reached"]);
        }
        steps.push(currentTerm.toString());
        previousTerm = currentTerm;
        currentTerm = reduce(currentTerm);
        step_count++;
    }

    return steps;
}


function reduce(term) {
    if (term instanceof Application) {
        if (term.function instanceof Expression) {
            return substitute(term.function.body, term.function.variable, term.argument);
        } else {
            const reducedFunc = reduce(term.function);
            if (reducedFunc !== term.function) {
                return new Application(reducedFunc, term.argument);
            } else {
                const reducedArg = reduce(term.argument);
                if (reducedArg !== term.argument) {
                    return new Application(term.function, reducedArg);
                } else {
                    return term;
                }
            }
        }
    } else if (term instanceof Expression) {
        const reducedBody = reduce(term.body);
        if (reducedBody !== term.body) {
            return new Expression(term.variable, reducedBody);
        } else {
            return term;
        }
    } else {
        return term;
    }
}

// // Update the evaluate function to use the single-step reduction
// function evaluate(term, maxSteps = 10) {
//     let currentTerm = term;
//     const steps = [currentTerm.toString()];
    
//     for (let step = 0; step < maxSteps; step++) {
//         const nextTerm = reduceOnce(currentTerm);
//         if (nextTerm.toString() === currentTerm.toString()) {
//             break; // Normal form reached
//         }
//         steps.push(nextTerm.toString());
//         currentTerm = nextTerm;
//     }
    
//     if (maxSteps > 0 && steps.length === maxSteps) {
//         steps.push("Infinite recursion reached");
//     }
    
//     return steps;
// }





function evaluateExpression() {
    counter = 0;
    
    const input = document.getElementById('input').value;
    const outputDiv = document.getElementById('output');
    const errorDiv = document.getElementById('error');
    const expandedDiv = document.getElementById('expanded');

    function evaluateSteps(result) {
        outputDiv.textContent = '';
        result.forEach((step, _) => {
            outputDiv.innerHTML += `<div class="step">${step}</div><br>`;
        });
        outputDiv.innerHTML += `<button id="hide-steps">Hide Evaluation Steps</button>`;
        document.getElementById('hide-steps').addEventListener('click', hideSteps);

        function hideSteps() {
            outputDiv.textContent = ''; 
            outputDiv.innerHTML = result[result.length - 1];
            outputDiv.innerHTML += `<br><button id="steps">Show Evaluation Steps</button>`;
            document.getElementById('steps').addEventListener('click', () => evaluateSteps(result));
        }
    }

    try {
        errorDiv.textContent = '';
        outputDiv.textContent = '';
        expandedDiv.style.display = 'none';
        outputDiv.style.textAlign = 'center';

        let expressionToEvaluate = expandSimpleSyntax(input);

        const term = parse(expressionToEvaluate);
        const result = evaluate(term);
        outputDiv.innerHTML = result[result.length - 1];
        outputDiv.innerHTML += `<br><br><button id="steps">Show Evaluation Steps</button>`;
        document.getElementById('steps').addEventListener('click', () => evaluateSteps(result));

    } catch (error) {
        errorDiv.textContent = `${error.message}`;
        outputDiv.textContent = '';
    }
}



let currentMode = 'simple';

function setMode(mode) {
    currentMode = mode;
    document.getElementById('simpleTab').classList.toggle('active', mode === 'simple');
    document.getElementById('advancedTab').classList.toggle('active', mode === 'advanced');
    document.getElementById('input').placeholder = mode === 'simple' ? 
        "Enter expression (e.g., 'add 1 2')" : 
        "Enter lambda calculus expression (e.g., 'λx.x')";
}

/**
 * 
 * Some helper functions to make things a bit easier
 * for the user.
 * 
 */

function numToChurch(num) {
    let churchExpr = 'λf.λx.';

    for (let i = 0; i < num; i++) {
        churchExpr += 'f(';
    }

    churchExpr += 'x' + ')'.repeat(num);
    return churchExpr;
}

function lambdaToBool(lambdaBool) {
    if (lambdaBool instanceof Expression && lambdaBool.variable.name === 'x') {
        if (lambdaBool.body instanceof Expression && lambdaBool.body.variable.name === 'y') {
            return lambdaBool.body.body instanceof Variable && lambdaBool.body.body.name === 'x';
        }
    }
    return false;
}

function booleanToLambdaTerm(bool) {
    const x = new Variable('x');
    const y = new Variable('y');
    return new Expression(x, new Expression(y, bool ? x : y));
}

function numToChurchTerm(num) {
    const f = new Variable('f');
    const x = new Variable('x');
    let body = x;
    for (let i = 0; i < num; i++) {
        body = new Application(f, body);
    }
    return new Expression(f, new Expression(x, body));
}
