
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
    
def check_proof(tree):
    sequent = tree["sequent"]
    proof = tree["proof"]
    premises = sequent["premises"]
    deduction_formula = sequent["deduction"]
    line_numbers = list(proof.keys())
    line_numbers.sort()
    for line_number in line_numbers:
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
                print(f"Proof Line Number: {line_number} with [premise] is Wrong! Premise Not Found in Sequent")
                return False
            
        ### check for [copy]
        if proof_line["explanation"]["rule"] == "copy":
            line_copied = proof_line["explanation"]["line"]
            if line_copied not in line_numbers:
                print(f"Proof Line Number: {line_number} with [copy] is Wrong! Line: {line_copied} does not exist")
                return False
            if not compare_formulae(proof_line["formula"], proof[line_copied]["formula"]):
                print(f"Proof Line Number: {line_number} with [copy] is Wrong!")
                
        ### check for [mp]
        if proof_line["explanation"]["rule"] == "mp":
            line_1 = proof_line["explanation"]["line-1"]
            line_2 = proof_line["explanation"]["line-2"]
            if line_1 not in line_numbers or line_2 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [mp] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_2['operation'] != 'implies_op':
                print(f"Proof Line Number: {line_number} with [mp] is Wrong! -> Expected in Line: {line_2}")
                return False
            if not compare_formulae(formula_1, formula_2['formula-1']) or not compare_formulae(formula_3, formula_2['formula-2']):
                print(f"Proof Line Number: {line_number} with [mp] is Wrong!")
                return False
            
        ### check for [mt]
        if proof_line['explanation']['rule'] == 'mt':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in line_numbers or line_2 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [mt] is Wrong! Invalid Line Numbers")
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_1['operation'] != 'implies_op':
                print(f"Proof Line Number: {line_number} with [mt] is Wrong! Expected  -> in line {line_1}")
                return False
            
            if formula_2["operation"] != 'not_op' or formula_3['operation'] != 'not_op':
                print(f"Proof Line Number: {line_number} with [mt] is Wrong! Expected ! in lines {line_2} and {line_number}")
                return False

            if not compare_formulae(formula_1['formula-2'], formula_2['formula']) or not compare_formulae(formula_1['formula-1'], formula_3['formula']):
                print(f"Proof Line Number: {line_number} with [mt] is Wrong!")
                return False
            
        ### check for [and-in]
        if proof_line['explanation']['rule'] == 'and-in':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in line_numbers or line_2 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [and-in] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'and_op' or (not compare_formulae(formula_1, formula_3['formula-1'])) or not compare_formulae(formula_2, formula_3['formula-2']):
                print(f"Proof Line Number: {line_number} with [and-in] is Wrong!")
                return False
            
        ### check for [and-e1]
        if proof_line['explanation']['rule'] == 'and-e1':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [and-e1] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'and_op' or (not compare_formulae(formula_1['formula-1'], formula_2)):
                print(f"Proof Line Number: {line_number} with [and-e1] is Wrong!")
                return False
        
        ### check for [and-e2]
        if proof_line['explanation']['rule'] == 'and-e2':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [and-e2] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'and_op' or (not compare_formulae(formula_1['formula-2'], formula_2)):
                print(f"Proof Line Number: {line_number} with [and-e2] is Wrong!")
                return False
        
        ### check for [or-in1]
        if proof_line['explanation']['rule'] == 'or-in1':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [or-in1] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'or_op' or (not compare_formulae(formula_1, formula_2['formula-1'])):
                print(f"Proof Line Number: {line_number} with [or-in1] is Wrong!")
                return False
        
        ### check for [or-in2]
        if proof_line['explanation']['rule'] == 'or-in2':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [or-in2] is Wrong! Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'or_op' or (not compare_formulae(formula_1, formula_2['formula-2'])):
                print(f"Proof Line Number: {line_number} with [or-in2] is Wrong!")
                return False
            
        ### check for [lem]
        if proof_line['explanation']['rule'] == 'lem':
            formula = proof_line['formula']
            if formula['operation'] != 'or_op':
                print("Proof Line Number: {line_number} with [lem] is Wrong! \/ Expected")
                return False 
            if formula['formula-2']['operation'] != 'not_op':
                print("Proof Line Number: {line_number} with [lem] is Wrong! ! Expected in Second formula")
                return False
            if not compare_formulae(formula['formula-1'], formula['formula-2']['formula']):
                print(f"Proof Line Number: {line_number} with [lem] is Wrong!, Formulas not complementary!")
                return False
        
        ### check for [dneg-in]
        if proof_line['explanation']['rule'] == 'dneg-in':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [dneg-in] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_2['operation'] != 'not_op' or formula_2['formula']['operation'] != 'not_op' or (not compare_formulae(formula_1, formula_2['formula']['formula'])):
                print(f"Proof Line Number: {line_number} with [dneg-in] is Wrong! phi and (! (! phi)) expected")
                return False
        
        ### check for [deng-el]
        if proof_line['explanation']['rule'] == 'dneg-el':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [dneg-el] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'not_op' or formula_1['formula']['operation'] != 'not_op' or (not compare_formulae(formula_2, formula_1['formula']['formula'])):
                print(f"Proof Line Number: {line_number} with [dneg-el] is Wrong! (!(!phi)) and phi expected")
                return False              
 
        ### check for [neg-el]
        if proof_line['explanation']['rule'] == 'neg-el':
            line_1 = proof_line['explanation']['line-1']
            line_2 = proof_line['explanation']['line-2']
            if line_1 not in line_numbers or line_2 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [neg-el] is Wrong! Invalid Line Numbers")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof[line_2]['formula']
            formula_3 = proof_line['formula']
            if formula_3['operation'] != 'bottom':
                print(f'Proof Line Number: {line_number} with [neg-el] is Wrong! bottom expected')
                return False
            
            if formula_2['operation'] != 'not_op':
                print(f'Proof Line Number: {line_number} with [neg-el] is Wrong! ! expected in {line_2}')
                return False
            
            if not compare_formulae(formula_1, formula_2['formula']):
                print(f"Proof Line Number: {line_number} with [neg-el] is Wrong! phi and ! phi expected on {line_1}, {line_2} respectively.")
                return False
        
        ### check for [bot-el]
        if proof_line['explanation']['rule'] == 'bot-el':
            line_1 = proof_line['explanation']['line']
            if line_1 not in line_numbers:
                print(f"Proof Line Number: {line_number} with [bot-el] is Wrong, Invalid Line Number")
                return False
            formula_1 = proof[line_1]['formula']
            formula_2 = proof_line['formula']
            if formula_1['operation'] != 'bottom':
                print(f"Proof Line Number: {line_number} with [bot-el] is Wrong, bottom expected on line {line_1}")
                return False 
                
            

                
            
 

    return True