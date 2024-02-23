package sms.synthesizer;

import java.util.ArrayList;
import java.util.HashSet;

import sms.benchmark.Benchmark;
import sms.multipleInvocation.MIUtils;
import sms.programNode.Node;
import sms.utils.Utils;
import sms.verification.Verifier;

public class Preprocessor {
	
public static String[] extractSubprograms(Benchmark benchmark) {
		


		String assertionString = benchmark.getAssertionString().substring(0);
		
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			while (assertionString.contains(" " + benchmark.getVariableNames()[i] + " ")) {
				assertionString = assertionString.replace(" " + 
			benchmark.getVariableNames()[i] + " ", " " + benchmark.getSynthesisVariableNames()[i] + " ");
			}
			assertionString = assertionString.replace(benchmark.getVariableNames()[i] + ")", benchmark.getSynthesisVariableNames()[i] + ")");
		}
		
		HashSet<String> definedFunctionsSet = new HashSet<String>();
		if (benchmark.getDefinedFunctionNames() != null) {
			//definedFunctionsSet = new HashSet<String>();
			for (int i = 0; i < benchmark.getDefinedFunctionNames().length; i++) {
				//////System.out.println(benchmark.getDefinedFunctionNames()[i].trim());
				definedFunctionsSet.add(benchmark.getDefinedFunctionNames()[i].trim());
			}
		}
		definedFunctionsSet.add(benchmark.getFunctionName());
		
		Node constraintsAsProg = Node.buildNodeFromProgramString(assertionString, definedFunctionsSet);

		String functionName = benchmark.getFunctionName();
		HashSet<String> extractedPrograms = new HashSet<>();
		ArrayList<Node> nodes = new ArrayList<>();
		nodes.add(constraintsAsProg);
		while (!nodes.isEmpty()) {
			Node n = nodes.remove(0);
			String parentType = n.toString();
			if (childrenContainTargetFunction(n.children, functionName)) {
				for (int i = 0; i < n.children.length; i++) {
					Node child = n.children[i];
					String childType = child.toString();
					if (childType.equals(functionName)) {
						continue;
					} else if (parentType.equals(">=") || parentType.equals("distinct")) {
						extractedPrograms.add("(+ " + child.makeLispTree() + " 1)");
					} else if (parentType.equals("<=")) {
						extractedPrograms.add("(- " + child.makeLispTree() + " 1)");
					} else {
						extractedPrograms.add(child.makeLispTree());
					}
				}
			} else {
				for (int i = 0; i < n.children.length; i++) {
					nodes.add(n.children[i]);
				}
			}

		}
		
		//The below cover edge cases for MI distinct and symmetry
		//where no specific program is required e.g. spec with one constraint
		//(constraint (= (f x y) (f y x))).
		if (benchmark.getInvocations().size() > 1) {
			for (int i = 0; i < benchmark.getSynthesisVariableNames().length; i++) {
				extractedPrograms.add(benchmark.getSynthesisVariableNames()[i]);

			}
		}
		
		//Covers reflexive edge case e.g. spec with one constraint
		//(constraint (= (f x y) (f x y)))
		extractedPrograms.add("0");
		

		return extractedPrograms.toArray(new String[extractedPrograms.size()]);
	}

private static boolean childrenContainTargetFunction(Node[] children, String targetFunction) {
	
	for (int i = 0; i < children.length; i++) {
		if (children[i].toString().equals(targetFunction)) {
			return true;
		}
	}
	
	
	
	return false;
}

public static String transformSpecToSingleAssigningInvocation(Benchmark benchmark) {
		


		String assertionString = benchmark.getAssertionString().substring(0);
		
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			while (assertionString.contains(" " + benchmark.getVariableNames()[i] + " ")) {
				assertionString = assertionString.replace(" " + 
			benchmark.getVariableNames()[i] + " ", " " + benchmark.getSynthesisVariableNames()[i] + " ");
			}
			assertionString = assertionString.replace(benchmark.getVariableNames()[i] + ")", benchmark.getSynthesisVariableNames()[i] + ")");
		}
		
		HashSet<String> definedFunctionsSet = new HashSet<String>();
		if (benchmark.getDefinedFunctionNames() != null) {
			//definedFunctionsSet = new HashSet<String>();
			for (int i = 0; i < benchmark.getDefinedFunctionNames().length; i++) {
				//////System.out.println(benchmark.getDefinedFunctionNames()[i].trim());
				definedFunctionsSet.add(benchmark.getDefinedFunctionNames()[i].trim());
			}
		}
		definedFunctionsSet.add(benchmark.getFunctionName());
		
		Node constraintsAsProg = Node.buildNodeFromProgramString(assertionString, definedFunctionsSet);

		
		
		String[] variables = benchmark.getVariableNames();
		ArrayList<String> assigningInvocation = new ArrayList<>();
		String fcs = "(" + benchmark.getFunctionName();
		for (int i = 0; i < variables.length; i++) {
			assigningInvocation.add(variables[i]);
			fcs += " " + variables[i];
		}
		
		fcs += ")";
		
		fcs = MIUtils.transformProgramFromInvocationToTempVars(fcs, assigningInvocation);
		

		
		ArrayList<String> comps = new ArrayList<>();
		comps.add("<="); comps.add(">="); 
		comps.add(">"); comps.add("<");
		comps.add("="); comps.add("distinct");
		String functionName = benchmark.getFunctionName();
		ArrayList<Node> nodes = new ArrayList<>();
		nodes.add(constraintsAsProg);
		while (!nodes.isEmpty()) {
			Node n = nodes.remove(0);
			String nodeType = n.toString();
			////System.out.println(nodeType);
			if (comps.contains(nodeType)) {
				////System.out.println("Howdy");
				Node childOne = n.children[0];
				Node childTwo = n.children[1];
				
				if (childOne.toString().equals(functionName) && !childTwo.toString().equals(functionName)) {
				 n.children = replacementChildren(childOne, childTwo, fcs, assigningInvocation, definedFunctionsSet);
				} else if(!childOne.toString().equals(functionName) && childTwo.toString().equals(functionName)) {
				n.children = replacementChildren(childTwo, childOne, fcs, assigningInvocation, definedFunctionsSet);
				} else if(childOne.toString().equals(functionName) && childTwo.toString().equals(functionName)) {
				n.children = replacementChildren(childOne, childTwo, fcs, assigningInvocation, definedFunctionsSet);
				}
			} else {
				for (int i = 0; i < n.children.length; i++) {
					nodes.add(n.children[i]);
				}
			}
		}

		return MIUtils.transformProgramFromTempVarsToInvocation(constraintsAsProg.makeLispTree(), assigningInvocation);
	}



public static String transformToRemoveGteLtes(Benchmark benchmark) {
	
//	////System.out.println("Removing cons and tauts");
	System.out.println("Changes >= and <= to or statement version");
	
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	
	//System.out.println(modifiedAssertionString);
	String[] operators = {"<=", ">="};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				
				//Using the nextPredicateInstance array, we get the substrings from the full program that are immediately before the
				//operator function and immediately after.
			/*	System.out.println("Operator " + operators[i]);
				System.out.println(nextPredicateInstance[0]);
				System.out.println(nextPredicateInstance[1]);*/
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				
				//System.out.println(prePred);
			//	System.out.println(pred);
				int start = 4;
			
				/*
				if (pred.substring(0,4).equals("("+operators[i]+ "= ")) {
					start = 4;
				}
				*/
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = 
						extractedOne.length() > checker.length() 
						&& extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
						&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

				if (check) {
					if (operators[i].equals("<=")) { 
						String orString = "(or (< " + extractedOne + " " + extractedTwo + ") (= " + extractedOne + " " + extractedTwo + "))";
						j = orString.length()-1;
						modifiedAssertionString = prePred + orString + postPred;
						//System.out.println(modifiedAssertionString);
					} else {
						String orString = "(or (> " + extractedOne + " " + extractedTwo + ") (= " + extractedOne + " " + extractedTwo + "))";
						j = orString.length()-1;
						modifiedAssertionString = prePred + orString + postPred;
					}
					//Right, here is where we perform the check
				} else {
					j = nextPredicateInstance[1];
				}
				
				

			}

		}
		

	}
	
	//////System.out.println("Escaped");
	return modifiedAssertionString;
	
}


public static void lteGteKiller(Benchmark benchmark, Verifier verifier, ArrayList<String> satSet) {
	
	System.out.println("Let's get em");
	
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	
	//System.out.println(modifiedAssertionString);
	String[] operators = {"="};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				
				//At the point this function is called, we know that there are no <=/>= left in the spec.
				int start = operators[i].length() + 2;
			
				

				
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = 
						extractedOne.length() > checker.length() 
						&& extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
						&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

						
					
				if (check) {
					String tmpAssertionString = prePred + " false " + postPred;
					//the ones where this doesn't work are where we have an OR i.e. it could be this or something else.
					System.out.println("Trying edit "  + tmpAssertionString);
					verifier.setAssertionString(tmpAssertionString);
					if (verifier.verifyMIPartials(satSet, null, null)) {
						modifiedAssertionString = prePred + " false " + postPred;

						j = nextPredicateInstance[1] - pred.length() + " false ".length() + 1;
						//System.out.println(modifiedAssertionString.substring(j));
						//System.out.println()
						//j = " false ".length()-1; //It'll be the same length for < or >
						//modifiedAssertionString = prePred + " false " + postPred;
					} else {
						
						j = nextPredicateInstance[1];
					}
					
				} else {
					j = nextPredicateInstance[1];
				}
				
				
				//System.out.println("j is " + j);
				
				

			}

		}
		

	}
	
	verifier.setAssertionString(modifiedAssertionString);
	benchmark.setAssertionString(modifiedAssertionString);
	//////System.out.println("Escaped");
	
}

public static String transformToJustNeccEqs(Benchmark benchmark) {
	
	System.out.println("Just Necc Eqs");
	
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	
	//System.out.println(modifiedAssertionString);
	String[] operators = {"="};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				
				//At the point this function is called, we know that there are no <=/>= left in the spec.
				int start = 3;
			
				

				
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = 
						extractedOne.length() > checker.length() 
						&& extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
						&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

				if (check) {
					//the ones where this doesn't work are where we have an OR i.e. it could be this or something else.
					System.out.println("Hello");
					if (Verifier.verifyEditedAssertionImpliesOriginal(prePred + " false " + postPred, benchmark)) {
						boolean hmm = Verifier.verifyEditedAssertionImpliesOriginal(prePred + " true " + postPred, benchmark);
						System.out.println("What happened? " +hmm);
						j = nextPredicateInstance[1];
						//j = " false ".length()-1; //It'll be the same length for < or >
						//modifiedAssertionString = prePred + " false " + postPred;
					} else {
						j = nextPredicateInstance[1];
					}
					
				} else {
					j = nextPredicateInstance[1];
				}
				
				

			}

		}
		

	}
	
	//////System.out.println("Escaped");
	return modifiedAssertionString;
	
}
/*
public static String transformToJustNecessaryGtLtMI(Benchmark benchmark) {
	
	System.out.println("Just Necc GT LT");
	
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	
	//System.out.println(modifiedAssertionString);
	String[] operators = {"<", ">"};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				
				if (!pred.substring(0,4).equals("("+operators[i]+ "= ")) {
					j = nextPredicateInstance[1];
					break;
				}
				
				int start = 4;
			
				

				
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = 
						extractedOne.length() > checker.length() 
						&& extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
						&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

				if (check) {
					if (Verifier.verifyEditedAssertionImpliesOriginal(prePred + "(" + operators[i] + " " + pred.substring(start) + postPred, benchmark)) {
						j = ("(< " + pred.substring(start)).length()-1; //It'll be the same length for < or >
						modifiedAssertionString = prePred + "(" + operators[i] + " " + pred.substring(start) + postPred;
					} else {
						j = nextPredicateInstance[1];
					}
					
				} else {
					j = nextPredicateInstance[1];
				}
				
				

			}

		}
		

	}
	
	//////System.out.println("Escaped");
	return modifiedAssertionString;
	
}

public static String transformToJustNecessaryComparisons(Benchmark benchmark) {
	
//	////System.out.println("Removing cons and tauts");
	System.out.println("Just Nec");
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	String[] operators = {">", "<", "<=", ">=", "=", "distinct"};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				
				int start = operators[i].length() + 2;
				//Using the nextPredicateInstance array, we get the substrings from the full program that are immediately before the
				//operator function and immediately after.
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = extractedOne.length() > checker.length() && extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");
				check = check ||
						(extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " "));
				
				//Substitute in false and true to see if these are contradictions or tautologies. If they are, modify the
				//program String to just be false/true respectively where the operator used to be, and then calculate the new
				//position for j
				if (check) {
					if (Verifier.verifyEditedAssertionImpliesOriginal(prePred + " false " + postPred, benchmark)) {
						j = (prePred + " false ").length() - 1;
						modifiedAssertionString = prePred + " false " + postPred;
					} else if (Verifier.verifyEditedAssertionImpliesOriginal(prePred + " true " + postPred,
							benchmark)) {
						j = (prePred + " true ").length() - 1;
						modifiedAssertionString = prePred + " true " + postPred;
					} else {
						// If we've gotten here we didn't need to modify, set J to just the endIndex
						// from the parentheses so this
						// instance of the operator is skipped over on next call of
						// findNextPredicateInstance.
						j = nextPredicateInstance[1];
					}
				} else {
					j = nextPredicateInstance[1];
				}

			}

		}
		

	}
	
	//////System.out.println("Escaped");
	return modifiedAssertionString;
	
}


public static String transformToRemoveGtLtCase(Benchmark benchmark) {
	
//	////System.out.println("Removing cons and tauts");
	
	String modifiedAssertionString = benchmark.getAssertionString().substring(0);
	
	//System.out.println(modifiedAssertionString);
	String[] operators = {"<", ">"};
	
	//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
	//in Sygus have these.
	for (int i = 0; i < operators.length; i++) {

		//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
		int j = 0;
		while (true) {
			//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
			//if it is does not exist returns null and we break this inner loop 
			int[] nextPredicateInstance = Utils.findNextPredicateInstance(modifiedAssertionString, operators[i],
					j);

			if (nextPredicateInstance == null) {
				//operator wasn't found, so break this inner loop and move to the next operator
				break;
			} else {
				String prePred = modifiedAssertionString.substring(0, nextPredicateInstance[0]);
				String pred = modifiedAssertionString.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
				String postPred = modifiedAssertionString.substring(nextPredicateInstance[1] + 1);
				
				
				int start = 3;
				
				if (pred.substring(0,4).equals("("+operators[i]+ "= ")) {
					start = 4;
				}
				
				

				
				
				String extractedOne = Utils.extractNextFunction(pred.substring(start, pred.length()));
				//System.out.println("Extracted 1: " + extractedOne);
				String extractedTwo = Utils.extractNextFunction(pred.substring(start+extractedOne.length()+1, pred.length()));
				//System.out.println("Extracted 2: " + extractedTwo);
				String functionName = benchmark.getFunctionName();
				String checker = "(" + functionName + " ";
				
				boolean check = 
						extractedOne.length() > checker.length() 
						&& extractedTwo.length() > checker.length() 
						&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
						&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

				if (check) {
					if (pred.substring(0,4).equals("("+operators[i]+ "= ")){
						j = (prePred + " false ").length() - 1;
						modifiedAssertionString = prePred + " false " + postPred;
					} else {
						j = (prePred + " true ").length() - 1;
						modifiedAssertionString = prePred + " false " + postPred;
					}
					
				} else {
					j = nextPredicateInstance[1];
				}
				
				

			}

		}
		

	}
	
	//////System.out.println("Escaped");
	return modifiedAssertionString;
	
}
*/

private static Node[] replacementChildren(Node functionChild, Node valueChild, String replacementFunction, ArrayList<String> aInv,
			HashSet<String> definedFunctionsSet) {
		
		ArrayList<String> oInv = new ArrayList<>();
		for (int i = 0; i < functionChild.children.length; i++) {
			oInv.add(
			MIUtils.transformProgramFromTempVarsToInvocation(functionChild.children[i].makeLispTree(), aInv));
		}
		//System.out.print(false);
		String valProg = MIUtils.transformProgramFromTempVarsToInvocation(valueChild.makeLispTree(), aInv);
		////System.out.println("val prog 2 " + valProg);
		valProg = MIUtils.transformProgramFromInvocationToTempVars(valProg, oInv);
		
		//System.out.println("val prog " + valProg);
		////System.out.println("val prog 3 "  + valProg);
		//System.out.println("Replacement function is " + replacementFunction);
		Node[] replacements = new Node[2];
		replacements[0] = Node.buildNodeFromProgramString(replacementFunction, definedFunctionsSet);
		replacements[1] = Node.buildNodeFromProgramString(valProg, definedFunctionsSet);
		//System.out.println("The replacement One " +replacements[0].makeLispTree());
		//System.out.println("The replacement Two " + replacements[1].makeLispTree());
		return replacements;
	}



//private static Node[]
 
public static boolean meetsSameVariablesAssumptions(Benchmark benchmark) {
	String[] variables = benchmark.getVariableNames();
	HashSet<String> variablesSet = new HashSet<>();
	for (int i = 0; i < variables.length; i++) {
		variablesSet.add(variables[i]);
	}
	
	for (ArrayList<String> inv : benchmark.getInvocations()) {
		HashSet<String> foundSoFar = new HashSet<>();
		for (int i = 0; i < inv.size(); i++) {
			if (!variablesSet.contains(inv.get(i))) {
				return false;
			}
			foundSoFar.add(inv.get(i));
		}
		
		if (foundSoFar.size() != variablesSet.size()) {
			return false;
		}
	}
	
	return true;
}
public static void main(String[] args) throws Exception {
	//String benchmarkFile = "src/main/resources/MIBenchmarks/mi_explainer.sl";
	String benchmarkFile = "src/main/resources/SIBenchmarks/fg_array_search_20.sl";
	Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
	
	////System.out.println("Meets Assumptions?: " + Preprocessor.meetsSameVariablesAssumptions(benchmark));
	
	String transform = Preprocessor.transformSpecToSingleAssigningInvocation(benchmark);
	benchmark.setAssertionString(transform);
	String[] correctTerms = Preprocessor.extractSubprograms(benchmark);
	for (int i = 0; i < correctTerms.length; i++) {
		//System.out.println(correctTerms[i]);
	}
}
	
	
}
