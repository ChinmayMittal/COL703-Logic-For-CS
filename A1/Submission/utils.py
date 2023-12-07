
def compare_formulae(formula_1, formula_2):
    if formula_1["operation"] == "atomic_prop":
        if formula_2["operation"] != "atomic_prop":
            return False
        else:
            return formula_1["name"] == formula_2["name"]
    if formula_2["operation"] == "atomic_prop":
        if formula_1["operation"] != "atomic_prop":
            return False
        else:
            return formula_1["name"] == formula_2["name"]
    
    if formula_1["operation"] in ["and_op", "or_op", "implies_op"]:
        return (formula_1["operation"] == formula_2["operation"] and 
                compare_formulae(formula_1["formula-1"], formula_2["formula-1"]) and 
                compare_formulae(formula_1["formula-2"], formula_2["formula-2"]))
    
    if formula_1["operation"] == "bottom":
        return formula_2["operation"] == "bottom"
    
    if formula_1["operation"] == "not_op":
        return formula_2["operation"] == "not_op" and compare_formulae(formula_1["formula"], formula_2["formula"])

def find_assumption_scopes(proof):
    line_numbers = list(proof.keys())
    line_numbers.sort()
    assumption_scopes = dict() ### start-end
    for line_number in line_numbers:
        proof_line = proof[line_number]
        ### assumptions
        if proof_line['explanation']['rule'] == 'assumption':
            assumption_scopes[line_number] = -1
            
        ### rules indicating closure of a box
        if proof_line['explanation']['rule'] == 'impl-in':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if range_start not in assumption_scopes or assumption_scopes[range_start] != -1:
                return None
            assumption_scopes[range_start] = range_end
            
        if proof_line['explanation']['rule'] == 'neg-in':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if range_start not in assumption_scopes or assumption_scopes[range_start] != -1:
                return None
            assumption_scopes[range_start] = range_end
        
        if proof_line['explanation']['rule'] == 'pbc':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if range_start not in assumption_scopes or assumption_scopes[range_start] != -1:
                return None
            assumption_scopes[range_start] = range_end
        
        if proof_line['explanation']['rule'] == 'or-el':
            range_start_1 = int(proof_line['explanation']['range-1']['start'].value)
            range_end_1 = int(proof_line['explanation']['range-1']['end'].value)
            range_start_2 = int(proof_line['explanation']['range-2']['start'].value)
            range_end_2 = int(proof_line['explanation']['range-2']['end'].value)
            if range_start_1 not in assumption_scopes or assumption_scopes[range_start_1] != -1:
                return None
            if range_start_2 not in assumption_scopes or assumption_scopes[range_start_2] != -1:
                return None
            assumption_scopes[range_start_1] = range_end_1
            assumption_scopes[range_start_2] = range_end_2
            
    open_assumption = any(value == -1 for value in assumption_scopes.values())
    if open_assumption:
        return None
            
    return assumption_scopes
        
    
def check_proof(tree):
    sequent = tree["sequent"]
    proof = tree["proof"]
    premises = sequent["premises"]
    deduction_formula = sequent["deduction"]
    line_numbers = list(proof.keys())
    line_numbers.sort()
    assumption_scopes = find_assumption_scopes(proof)
    if assumption_scopes is None:
        return False ### some assumption not closed
    in_scope_proof_lines = []
    # print("Assumption Scopes", assumption_scopes)
    assumption_ends = [v for k, v in assumption_scopes.items()]
    reverse_assumption_scopes = {v:k for k, v in assumption_scopes.items()}
    if not compare_formulae(deduction_formula, proof[line_numbers[-1]]['formula']):
        # print("Last Line should have the formula to be proved")
        return False

    for line_number in line_numbers:
        # print(f"Scope at Line: {line_number} => {in_scope_proof_lines}")
        proof_line = proof[line_number]
        
        ### check for [premise]
        if proof_line["explanation"]["rule"] == "premise":
            premise_formula = proof_line["formula"]
            found = False
            for premise in premises:
                if(compare_formulae(premise, premise_formula)):
                    found = True
                    break
            if not found:
                # print(f"Proof Line Number: {line_number} with [premise] is Wrong! Premise Not Found in Sequent")
                return False
            
        ### check for [copy]
        if proof_line["explanation"]["rule"] == "copy":
            line_copied = proof_line["explanation"]["line"]
            if line_copied not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [copy] is Wrong! Line: {line_copied} Not in Scope")
                return False
            if not compare_formulae(proof_line["formula"], proof[line_copied]["formula"]):
                # print(f"Proof Line Number: {line_number} with [copy] is Wrong!")
                return False
                
        ### check for [mp]
        if proof_line["explanation"]["rule"] == "mp":
            line_1 = proof_line["explanation"]["line-1"]
            line_2 = proof_line["explanation"]["line-2"]
            if line_1 not in in_scope_proof_lines or line_2 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [mp] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_2['operation'] != 'implies_op':
                # print(f"Proof Line Number: {line_number} with [mp] is Wrong! -> Expected in Line: {line_2}")
                return False
            if not compare_formulae(formula_1, formula_2['formula-1']) or not compare_formulae(formula_3, formula_2['formula-2']):
                # print(f"Proof Line Number: {line_number} with [mp] is Wrong!")
                return False
            
        ### check for [mt]
        if proof_line['explanation']['rule'] == 'mt':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in in_scope_proof_lines or line_2 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [mt] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_1['operation'] != 'implies_op':
                # print(f"Proof Line Number: {line_number} with [mt] is Wrong! Expected  -> in line {line_1}")
                return False
            
            if formula_2["operation"] != 'not_op' or formula_3['operation'] != 'not_op':
                # print(f"Proof Line Number: {line_number} with [mt] is Wrong! Expected ! in lines {line_2} and {line_number}")
                return False

            if not compare_formulae(formula_1['formula-2'], formula_2['formula']) or not compare_formulae(formula_1['formula-1'], formula_3['formula']):
                # print(f"Proof Line Number: {line_number} with [mt] is Wrong!")
                return False
            
        ### check for [and-in]
        if proof_line['explanation']['rule'] == 'and-in':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in in_scope_proof_lines or line_2 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [and-in] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'and_op' or (not compare_formulae(formula_1, formula_3['formula-1'])) or not compare_formulae(formula_2, formula_3['formula-2']):
                # print(f"Proof Line Number: {line_number} with [and-in] is Wrong!")
                return False
            
        ### check for [and-e1]
        if proof_line['explanation']['rule'] == 'and-e1':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [and-e1] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'and_op' or (not compare_formulae(formula_1['formula-1'], formula_2)):
                # print(f"Proof Line Number: {line_number} with [and-e1] is Wrong!")
                return False
        
        ### check for [and-e2]
        if proof_line['explanation']['rule'] == 'and-e2':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [and-e2] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'and_op' or (not compare_formulae(formula_1['formula-2'], formula_2)):
                # print(f"Proof Line Number: {line_number} with [and-e2] is Wrong!")
                return False
        
        ### check for [or-in1]
        if proof_line['explanation']['rule'] == 'or-in1':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [or-in1] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'or_op' or (not compare_formulae(formula_1, formula_2['formula-1'])):
                # print(f"Proof Line Number: {line_number} with [or-in1] is Wrong!")
                return False
        
        ### check for [or-in2]
        if proof_line['explanation']['rule'] == 'or-in2':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [or-in2] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'or_op' or (not compare_formulae(formula_1, formula_2['formula-2'])):
                # print(f"Proof Line Number: {line_number} with [or-in2] is Wrong!")
                return False
            
        ### check for [lem]
        if proof_line['explanation']['rule'] == 'lem':
            formula = proof_line['formula']
            if formula['operation'] != 'or_op':
                # print("Proof Line Number: {line_number} with [lem] is Wrong! \/ Expected")
                return False 
            if formula['formula-2']['operation'] != 'not_op':
                # print("Proof Line Number: {line_number} with [lem] is Wrong! ! Expected in Second formula")
                return False
            if not compare_formulae(formula['formula-1'], formula['formula-2']['formula']):
                # print(f"Proof Line Number: {line_number} with [lem] is Wrong!, Formulas not complementary!")
                return False
        
        ### check for [dneg-in]
        if proof_line['explanation']['rule'] == 'dneg-in':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [dneg-in] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'not_op' or formula_2['formula']['operation'] != 'not_op' or (not compare_formulae(formula_1, formula_2['formula']['formula'])):
                # print(f"Proof Line Number: {line_number} with [dneg-in] is Wrong! phi and (! (! phi)) expected")
                return False
        
        ### check for [deng-el]
        if proof_line['explanation']['rule'] == 'dneg-el':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [dneg-el] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'not_op' or formula_1['formula']['operation'] != 'not_op' or (not compare_formulae(formula_2, formula_1['formula']['formula'])):
                # print(f"Proof Line Number: {line_number} with [dneg-el] is Wrong! (!(!phi)) and phi expected")
                return False              
 
        ### check for [neg-el]
        if proof_line['explanation']['rule'] == 'neg-el':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in in_scope_proof_lines or line_2 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [neg-el] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'bottom':
                # print(f'Proof Line Number: {line_number} with [neg-el] is Wrong! bottom expected')
                return False
            
            if formula_2['operation'] != 'not_op':
                # print(f'Proof Line Number: {line_number} with [neg-el] is Wrong! ! expected in {line_2}')
                return False
            
            if not compare_formulae(formula_1, formula_2['formula']):
                # print(f"Proof Line Number: {line_number} with [neg-el] is Wrong! phi and ! phi expected on {line_1}, {line_2} respectively.")
                return False
        
        ### check for [bot-el]
        if proof_line['explanation']['rule'] == 'bot-el':
            line_1 = proof_line['explanation']['line']
            if line_1 not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [bot-el] is Wrong, Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'bottom':
                # print(f"Proof Line Number: {line_number} with [bot-el] is Wrong, bottom expected on line {line_1}")
                return False 
        
        ### check for [impl-in]
        if proof_line['explanation']['rule'] == 'impl-in':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if (range_start, range_end) not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} is invalid, range: {range_start}-{range_end} out of scope")
                return False
            formula_1 = proof[range_start]['formula']
            formula_2 = proof[range_end]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'implies_op':
                # print(f"Proof Line Number: {line_number} is invalid, -> expected in line {line_number}")
                return False
            if proof[range_start]['explanation']['rule'] != 'assumption':
                # print(f"Proof Line Number: {line_number} is invalid, line {range_start} is expected to be an assumption")
                return False
            if (not compare_formulae(formula_3['formula-1'], formula_1)) or (not compare_formulae(formula_3['formula-2'], formula_2)):
                # print(f"Proof Line Number: {line_number} with [impl-in] is Wrong")
                return False
            
        ### check for [pbc]
        if proof_line['explanation']['rule'] == 'pbc':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if (range_start, range_end) not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [pbc] is invalid, range: {range_start}-{range_end} out of scope")
                return False
            formula_1 = proof[range_start]['formula']
            formula_2 = proof[range_end]['formula']
            formula_3 = proof_line['formula']
            if formula_1['operation'] != 'not_op':
                # print(f"Proof Line Number: {line_number} is invalid, ! expected in line {range_start}")
                return False
            if proof[range_start]['explanation']['rule'] != 'assumption':
                # print(f"Proof Line Number: {line_number} with [pbc] is invalid, line {range_start} is expected to be an assumption")
                return False
            if (not compare_formulae(formula_3, formula_1['formula'])) or formula_2['operation'] != 'bottom':
                # print(f"Proof Line Number: {line_number} with [pbc] is Wrong")
                return False
            
        ### check for [neg-in]
        if proof_line['explanation']['rule'] == 'neg-in':
            range_start = int(proof_line['explanation']['range']['start'].value)
            range_end = int(proof_line['explanation']['range']['end'].value)
            if (range_start, range_end) not in in_scope_proof_lines:
                # print(f"Proof Line Number: {line_number} with [neg-in] is invalid, range: {range_start}-{range_end} out of scope")
                return False
            formula_1 = proof[range_start]['formula']
            formula_2 = proof[range_end]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'not_op':
                # print(f"Proof Line Number: {line_number} is invalid, ! expected in line {line_number}")
                return False
            if proof[range_start]['explanation']['rule'] != 'assumption':
                # print(f"Proof Line Number: {line_number} with [neg-in] is invalid, line {range_start} is expected to be an assumption")
                return False
            if (not compare_formulae(formula_3['formula'], formula_1)) or formula_2['operation'] != 'bottom':
                # print(f"Proof Line Number: {line_number} with [neg-in] is Wrong")
                return False
        
        ### check for [or-el]
        if proof_line['explanation']['rule'] == 'or-el':
            line_1 = proof_line['explanation']['line']
            range1_start = int(proof_line['explanation']['range-1']['start'].value)
            range1_end = int(proof_line['explanation']['range-1']['end'].value)
            range2_start = int(proof_line['explanation']['range-2']['start'].value)
            range2_end = int(proof_line['explanation']['range-2']['end'].value)
            if ((range1_start, range1_end) not in in_scope_proof_lines) or ((range2_start, range2_end) not in in_scope_proof_lines) or (line_1 not in in_scope_proof_lines):
                # print(f"Proof Line Number: {line_number} with [or-el] is Wrong!, Scope issues with {range1_start}-{range1_end} or {range2_start}-{range2_end} or {line_1}")
                return False
            formula_1 = proof[line_1]['formula'] ## phi \/ psi
            formula_2 = proof[range1_start]['formula'] ## phi
            formula_3 = proof[range1_end]['formula'] ### chi
            formula_4 = proof[range2_start]['formula'] ### psi 
            formula_5 = proof[range2_end]['formula'] ### chi 
            formula_6 = proof_line['formula'] ### chi
            if proof[range1_start]['explanation']['rule'] != 'assumption' or proof[range2_start]['explanation']['rule'] != 'assumption':
                # print(f"Proof Line Number: {line_number} with [or-el] is Wrong, lines {range1_start} and {range2_start} are expected to be assumptions")
                return False
            
            if formula_1['operation'] != 'or_op':
                # print(f"Proof Line Number: {line_number} with [or-el] is Wrong, line {line_1} is expected to have \/ ")
                return False

            if (not compare_formulae(formula_1['formula-1'], formula_2)) or (not compare_formulae(formula_1['formula-2'], formula_4)):
                # print(f"Proof Line Number: {line_number} with [or-el] is Wrong")
                return False
            
            if (not (compare_formulae(formula_3, formula_6))) or (not compare_formulae(formula_5, formula_6)):
                # print(f"Proof Line Number: {line_number} with [or-el] is Wrong")
                return False
        
        ### handle assumption scoping        
        in_scope_proof_lines.append(line_number)
        
        ### at end of an assumption box remove all lines in the scope of this box, for future proof lines
        if line_number in assumption_ends:
            while len(in_scope_proof_lines) > 0 and (in_scope_proof_lines[-1] != reverse_assumption_scopes[line_number]):
                in_scope_proof_lines.pop()
            if(in_scope_proof_lines[-1] == reverse_assumption_scopes[line_number]):
                in_scope_proof_lines.pop()
                ### the entire assumption box is now an entity which is added to the current scope
                in_scope_proof_lines.append((reverse_assumption_scopes[line_number], line_number))
        
    return True