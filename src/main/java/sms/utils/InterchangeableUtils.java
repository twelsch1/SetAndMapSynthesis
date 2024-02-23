package sms.utils;

import java.util.ArrayList;
import java.util.Collections;

import sms.benchmark.Benchmark;
import sms.multipleInvocation.MIUtils;
import sms.programNode.Node;
import sms.verification.Verifier;

public class InterchangeableUtils {

	
	public static void constructPermutationFromArray(
			  int n, ArrayList<String> elements, String delimiter, ArrayList<String> stringCSVs) {

			    if(n == 1) {
			    	//System.out.println("Hello");
			    	stringCSVs.add(buildCSV(elements));
			        //;
			    } else {
			        for(int i = 0; i < n-1; i++) {
			            constructPermutationFromArray(n - 1, elements, delimiter, stringCSVs);
			            if(n % 2 == 0) {
			                swap(elements, i, n-1);
			            } else {
			                swap(elements, 0, n-1);
			            }
			        }
			        constructPermutationFromArray(n - 1, elements, delimiter, stringCSVs);
			    }
			}
	
	
	private static void swap(ArrayList<String> elements, int a, int b) {
	    //String tmp = elements[a];
	    //elements[a] = elements[b];
	    //elements[b] = tmp;
	    Collections.swap(elements, a, b);
	}
	
	private static String buildCSV(ArrayList<String> elements) {
	    //String delimiterSpace = delimiter + " ";
		String CSV = "";
	    for(int i = 0; i < elements.size()-1; i++) {
	        CSV += elements.get(i) + ",";
	    }
	    CSV += elements.get(elements.size()-1);
	    
	    return CSV;
	}
	
	
	public static ArrayList<ArrayList<String>> calculateUniqueUnfixedPairs(ArrayList<String> permOne, ArrayList<String> permTwo) {
		
		ArrayList<ArrayList<String>> retVal = new ArrayList<>();
		
		for (int i = 0; i < permOne.size(); i++) {
			
			if (!permOne.get(i).equals(permTwo.get(i))) {
				ArrayList<String> ufvPair = new ArrayList<>();
				ufvPair.add(permOne.get(i));
				ufvPair.add(permTwo.get(i));
				
				Collections.sort(ufvPair);
				if (!retVal.contains(ufvPair)) {
					retVal.add(ufvPair);
				}
			}
			
			
		}
		
		
		
		
		
		return retVal;
		
		
		
	}
	
	public static boolean sharesCommonVariables(ArrayList<String> curr, ArrayList<String> group) {
		
		
		for (String s : curr) {
			if(group.contains(s)) {
				return true;
			}
		}
		
		return false;
		
	}
	
	public static ArrayList<ArrayList<String>> calculateUnfixedGroups(ArrayList<String> principalPermutation,
			ArrayList<ArrayList<String>> otherPermutations) {
		
		ArrayList<ArrayList<String>> UFGroups = new ArrayList<>();
		
		
		for (ArrayList<String> perm : otherPermutations) {
			
			ArrayList<ArrayList<String>> unfixedPairs = calculateUniqueUnfixedPairs(principalPermutation, perm);
			
			for (ArrayList<String> pair : unfixedPairs) {
				
				ArrayList<String> curr = pair; 
				boolean mergesIncomplete = true;
				
				while(mergesIncomplete) {
					mergesIncomplete = false;
					
					for (int i = 0; i < UFGroups.size(); i++) {
						if (sharesCommonVariables(curr, UFGroups.get(i))) {
							for (String s : UFGroups.get(i)) {
								if (!curr.contains(s)) {
									curr.add(s);
								}
							}
							UFGroups.remove(i); 
							mergesIncomplete = true;
							break;
						}
					}
					
					if (!mergesIncomplete) {
						UFGroups.add(curr);
					}
					
				}
				
				
			}
			
		}
		
		
		
		
		return UFGroups;
		
		
		
		
	}
	
	public static ArrayList<ArrayList<String>> sortUFGByLexicographicOrder(ArrayList<ArrayList<String>> OldUFG) {
		ArrayList<String> csvStrings = new ArrayList<>();
		ArrayList<ArrayList<String>> newUFG = new ArrayList<>();
		for (ArrayList<String> group : OldUFG) {
			Collections.sort(group);
			csvStrings.add(String.join(",", group));
		}
		
		Collections.sort(csvStrings);
		
		for (String s: csvStrings) {
			ArrayList<String> group = new ArrayList<>();
			String[] csvArr = s.split(",");
			for (int i = 0; i < csvArr.length; i++) {
				group.add(csvArr[i]);
			}
			newUFG.add(group);
			
			
		}
		
		
		
		return newUFG;
		
		
		
	}
	
	public static ArrayList<String> expandUFGPerms(String prefix, ArrayList<ArrayList<String>> permLists) {
		ArrayList<String> retVal = new ArrayList<>();
		
		ArrayList<ArrayList<String>> localPermLists = new ArrayList<ArrayList<String>>(permLists);
		ArrayList<String> currentList = localPermLists.remove(0);
		
		if (localPermLists.isEmpty()) {
			for (int i = 0; i < currentList.size(); i++) {
				retVal.add(prefix + currentList.get(i));
				
			}
			return retVal;
		}
		
		for (int i = 0; i < currentList.size(); i++) {
			retVal.addAll(expandUFGPerms(prefix + currentList.get(i) + ",", localPermLists));
		}
		
		
		return retVal;
		
	}
	
	public static ArrayList<ArrayList<String>> expandedUFGPermsAsLists(ArrayList<String> expandedUFGPermStrings) {
		ArrayList<ArrayList<String>> retVal = new ArrayList<>();
		
		for (String s : expandedUFGPermStrings) {
			ArrayList<String> ufgPermList = new ArrayList<>();
			String[] ufgPermArr = s.split(",");
			for (int i = 0; i < ufgPermArr.length; i++) {
				ufgPermList.add(ufgPermArr[i]);
			}
			retVal.add(ufgPermList);
		}
		
		
		return retVal;
	}
	
	public static String swapVariables(ArrayList<String> permOne, ArrayList<String> permTwo, String program) {
		String tmpString = transformProgramToTempVarsFromPermutation(program, permOne);
		return transformProgramFromTempVarsWithPermutation(tmpString, permTwo);
		
		
	}
	
	private static String transformProgramToTempVarsFromPermutation(String program, ArrayList<String> permutation) {
		String retVal = program;
		if (!program.contains("(")) {
			for (int i = 0; i < permutation.size(); i++) {
				if (retVal.equals(permutation.get(i))) {
					retVal = retVal.replace(permutation.get(i), "var" + (i+1) + ";");
					return retVal;
				}
				
			}

		} else {
			for (int i = 0; i < permutation.size(); i++) {
				//System.out.println(tmpSynthString);
				retVal = retVal.replace(" " + permutation.get(i) + " ", " var" + (i+1) + "; ");
				retVal = retVal.replace(permutation.get(i) + ")", "var" + (i+1) + ";)");
				retVal = retVal.replace("(" + permutation.get(i) + " ", "(var" + (i+1) + "; ");
				
				//System.out.println("um " + templateInvocation.get(i));
			}
		}
		
		return retVal;
	}
	
	
	public static String transformProgramFromTempVarsWithPermutation(String program, ArrayList<String> permutation) {
		String retVal = program;
		
		for (int i = 0; i < permutation.size(); i++) {
			retVal = retVal.replace("var" + (i+1) + ";", permutation.get(i));
		}
		
		return retVal;
		
	}
	
	public static ArrayList<String> filterToInterchangeableProgramsWithUFG(ArrayList<String> programsToFilter, ArrayList<ArrayList<String>> UFG) {
		
		ArrayList<String> retVal = new ArrayList<>();
		String pred = "(and true";
		for (int j = 0; j < UFG.size(); j++) {
			ArrayList<String> group = UFG.get(j);
			for (int i = 0; i < group.size()-1; i++) {
				pred += " (>= " + group.get(i) + " " + group.get(i+1) + ")";
			}
		}
		pred += ")";
		
		//System.out.println("Pred is " + pred);
		
		
		for (String s : programsToFilter) {
			if (s.contains(pred)) {
				retVal.add(s);
			}
		}
		
		return retVal;
		
		
	}
	
	public static String realizeInterchangeableProgram(String program, ArrayList<ArrayList<String>> UFG, ArrayList<ArrayList<String>>
	expandedUFGPerms) {
		

		String retVal = "";
		ArrayList<String> predicates = new ArrayList<>();
		ArrayList<String> programs = new ArrayList<>();
		String pred = "(and true";
		for (int j = 0; j < UFG.size(); j++) {
			ArrayList<String> group = UFG.get(j);
			for (int i = 0; i < group.size()-1; i++) {
				pred += " (>= " + group.get(i) + " " + group.get(i+1) + ")";
			}
		}
		pred += ")";
		
		
		for (int i = 0; i < expandedUFGPerms.size()-1; i++) {

			predicates.add(swapVariables(expandedUFGPerms.get(0), expandedUFGPerms.get(i), pred));
		}
		
		for (int i = 0; i < expandedUFGPerms.size(); i++) {
			programs.add(swapVariables(expandedUFGPerms.get(0), expandedUFGPerms.get(i), program));
		}
		
		String closingParens = "";
		
		for (int i = 0; i < predicates.size(); i++) {
			retVal += "(ite " + predicates.get(i) + " " + programs.get(i) + " ";
			closingParens += ")";
		}
		
		return retVal + programs.get(predicates.size()) + closingParens;
	}
	
	
	private static boolean variableIsFixed(ArrayList<String> programs, ArrayList<String> principalPermutation, int variableIndex) {
		
		ArrayList<String> tmpCheckPrograms = new ArrayList<>();
		for (String s : programs) {
			tmpCheckPrograms.add(
			MIUtils.transformProgramFromInvocationToTempVars(s, principalPermutation));
		}
		
		int[] variableValues = new int[principalPermutation.size()];
		
		for (int i = 0; i < variableValues.length; i++) {
			if (i == variableIndex) {
				variableValues[i] = 1;
			} else {
				variableValues[i] = 0; //I think it already is 0 by default but whatever
			}
			
			//System.out.print(variableValues[i] + " ");
		}
		//System.out.println();
		
		
		
		Node programNode =
				Node.buildNodeFromProgramString(
				Node.formatProgramStringForNode(tmpCheckPrograms.get(0)));
		
		//System.out.println("What program do I have? " + programNode.makeLispTree());
		int firstProgramCoeff = programNode.evaluate(variableValues);
		
		//System.out.println("First coefficient: " +
			//	firstProgramCoeff);
		
		for (int i = 1; i < programs.size(); i++) {
			int programCoeff = Node.buildNodeFromProgramString(
					Node.formatProgramStringForNode(tmpCheckPrograms.get(i))).evaluate(variableValues);
			
			//System.out.println("Coefficient " + i + ": " + programCoeff);
			
			if (firstProgramCoeff != programCoeff) {
				return false;
			}
		}
				
		
		
		return true;
		
	}
	
	public static ArrayList<String> calculateFixedVariablesFromPrograms(ArrayList<String> principalPermutation, ArrayList<String> programs) {
		
		ArrayList<String> fixedVariables = new ArrayList<String>();
		
		for (int i = 0; i < principalPermutation.size(); i++) {
			if (InterchangeableUtils.variableIsFixed(programs, principalPermutation, i)) {
				fixedVariables.add(principalPermutation.get(i));
			}
		}
		
		return fixedVariables;
	}
	
	public static void removeFixedVariablesFromGroup(ArrayList<String> fixedVariables, ArrayList<ArrayList<String>> UFG) {
		
		for (int i = 0; i < fixedVariables.size(); i++) {
			String variable = fixedVariables.get(i);
			
			for (ArrayList<String> group: UFG) {
				if (group.contains(variable)) {
					group.remove(variable);
				}
			}
		}

		
	}
	
	public static ArrayList<String> programsListWithoutITEs(ArrayList<String> programs) {
		ArrayList<String> retVal = new ArrayList<>();
		
		for (String s : programs) {
			if (!s.contains("(ite")) {
				retVal.add(s);
			}
		}
		
		return retVal;
		
	}
	
	public static ArrayList<String> programsListJustITEs(ArrayList<String> programs) {
		ArrayList<String> retVal = new ArrayList<>();
		
		for (String s : programs) {
			if (s.contains("(ite")) {
				retVal.add(s);
			}
		}
		
		return retVal;
		
	}
	
	public static String makeAllMICompsFalse(String functionName, String assertionString) {
		
		String modifiedAssertionString = assertionString;
		
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
					//String functionName = benchmark.getFunctionName();
					String checker = "(" + functionName + " ";
					
					boolean check = 
							extractedOne.length() > checker.length() 
							&& extractedTwo.length() > checker.length() 
							&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
							&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

							
						
					if (check) {
	//					String tmpAssertionString = prePred + " false " + postPred;
						//the ones where this doesn't work are where we have an OR i.e. it could be this or something else.
						//System.out.println("Trying edit "  + tmpAssertionString);
						//verifier.setAssertionString(tmpAssertionString);
						//(verifier.verifyMIPartials(satSet, null, null)) {
							modifiedAssertionString = prePred + "false" + postPred;

							j = nextPredicateInstance[1] - pred.length() + "false".length() + 1;
							//System.out.println(modifiedAssertionString.substring(j));
							//System.out.println()
							//j = " false ".length()-1; //It'll be the same length for < or >
							//modifiedAssertionString = prePred + " false " + postPred;
						
						
					} else {
						j = nextPredicateInstance[1];
					}
					
					
					//System.out.println("j is " + j);
					
					

				}

			}
			

		}
		
		//////System.out.println("Escaped");
		return modifiedAssertionString;
	}
	
	
	
public static boolean checkAllMICompsFalse(String functionName, String assertionString) {
		
		String modifiedAssertionString = assertionString;
		
		//System.out.println("We are now checking termination with " + assertionString);
		
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
					//String functionName = benchmark.getFunctionName();
					String checker = "(" + functionName + " ";
					
					boolean check = 
							extractedOne.length() > checker.length() 
							&& extractedTwo.length() > checker.length() 
							&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
							&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

							
						
					if (check) {
						return false;	
						
					} else {
						j = nextPredicateInstance[1];
					}
					
					
					//System.out.println("j is " + j);
					
					

				}

			}
			

		}
		
		//////System.out.println("Escaped");
		return true;
	}
	
	public static String blockOutNextConjunction(String assertionString, String replacementToken, String functionName, ArrayList<String> compsStore, Benchmark benchmark) {
		
		
		
		String modifiedAssertionString = assertionString;
		boolean firstEdit = true;
		
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
					//String functionName = benchmark.getFunctionName();
					String checker = "(" + functionName + " ";
					
					boolean check = 
							extractedOne.length() > checker.length() 
							&& extractedTwo.length() > checker.length() 
							&& extractedTwo.substring(0, functionName.length() + 2).equals("(" + functionName + " ")
							&& extractedOne.substring(0, functionName.length() + 2).equals("(" + functionName + " ");

							
					if (check && firstEdit) {
						modifiedAssertionString = prePred + replacementToken + postPred;
						j = nextPredicateInstance[1] - pred.length() + replacementToken.length() + 1;
						compsStore.add(pred);
						firstEdit = false;
						
						
					} else if (check) {
						String tmpAssertionString = prePred + replacementToken + postPred;
						//the ones where this doesn't work are where we have an OR i.e. it could be this or something else.
						System.out.println("Trying edit "  + tmpAssertionString);
						if (Verifier.verifyEditedEquivalentToOriginal(modifiedAssertionString, tmpAssertionString, benchmark)) {
							modifiedAssertionString = prePred + replacementToken + postPred;

							j = nextPredicateInstance[1] - pred.length() + replacementToken.length() + 1;
							compsStore.add(pred);
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
		
		return modifiedAssertionString;
		
		//verifier.setAssertionString(modifiedAssertionString);
		//benchmark.setAssertionString(modifiedAssertionString);
		//////System.out.println("Escaped");
		
	}
	
	
	
	public static String replaceReplacementTokensWithFalse(String assertionString, int numberOfTokens) {
		
		System.out.println("Number of tokens " + numberOfTokens);
		ArrayList<String> falses = new ArrayList<>();
		for (int i = 0; i < numberOfTokens; i++) {
			falses.add("false");
		}
		
		System.out.println("Number of falses " + falses.size());
		
		return replaceReplacementTokens(assertionString, falses);
	}
	
	public static String replaceReplacementTokens(String assertionString, ArrayList<String> replacements) {
		
		String modifiedAssertionString = assertionString;
		int i = 0;
		while(modifiedAssertionString.indexOf("(replacement_token ") != -1) {
			int startIndex = modifiedAssertionString.indexOf("(replacement_token ");
			int endIndex = startIndex + modifiedAssertionString.substring(startIndex).indexOf(")");
		
			
			
			//System.out.println("Start index " + startIndex);
			//System.out.println("End index " + endIndex);
			//System.out.println(
				//	"Replacing " +
					//modifiedAssertionString);
			
			modifiedAssertionString = modifiedAssertionString.substring(0, startIndex) +
			replacements.get(i) + modifiedAssertionString.substring(endIndex+1);
			i++;
			
				
			
		}
		
		
		
		//////System.out.println("Escaped");
		return modifiedAssertionString;
	}
	
	public static ArrayList<String> getVariablesFromComparisonAsCSV(String comparison, String functionName) {
		
		ArrayList<String> csvs = new ArrayList<>();
		String check = "(" + functionName;
		//com
		String funcOne = Utils.extractNextFunction(comparison.substring(comparison.indexOf(check)));
		csvs.add(
		extractParameters(funcOne.substring(check.length()+1)));
		
		String funcTwo = Utils.extractNextFunction(comparison.substring(comparison.lastIndexOf(check)));
		csvs.add(
				extractParameters(funcTwo.substring(check.length()+1)));
		//Array
		//System.out.println(extractParameters());
		//System.out.println(extractParameters(Utils.extractNextFunction(comparison.substring(comparison.lastIndexOf(check)))));
		
		
		
		return csvs;
	}
	
	
	private static String extractParameters(String varianceWithoutLeadingFunction) {
		
		
		String params = "";
		String sub = varianceWithoutLeadingFunction;
		String orig = sub;
		//////System.out.println(sub);
		int idx = 0;
		while (true) {
			String nextParam = Utils.extractNextFunction(sub);
			params += nextParam + ",";
			idx += nextParam.length() + 1;
			
			if (idx >= orig.length()) {
				break;
			}
			
			sub = orig.substring(idx);
			
		}
		
		return params.substring(0, params.length()-1);
		
	}
	
	public static ArrayList<ArrayList<String>> calculateUFGFromComparisons(ArrayList<String> comparisons, String functionName, ArrayList<String> principalPermutation) {
		ArrayList<String> csvStrings = new ArrayList<>();
		
		for (String s : comparisons) {
			ArrayList<String> compStrings = getVariablesFromComparisonAsCSV(s, functionName);
			for (String par : compStrings) {
				if (!csvStrings.contains(par)) {
					csvStrings.add(par);
				}
			}
		}
		
		ArrayList<ArrayList<String>> permutations = new ArrayList<>();
		for (String s : csvStrings) {
			String[] variables = s.split(",");
			ArrayList<String> permutation = new ArrayList<>();
			for (int i = 0; i < variables.length; i++) {
				permutation.add(variables[i]);
			}
			permutations.add(permutation);
		}
		
		return InterchangeableUtils.sortUFGByLexicographicOrder(
				InterchangeableUtils.calculateUnfixedGroups(principalPermutation, permutations));
	}
	
	
	public static void main(String[] args) throws Exception {
		
		String comparison =
		"(= (f x y) (f y x))";
		
		ArrayList<String> comparisons = new ArrayList<>();
		comparisons.add(comparison);
		
		String functionName = "f";
		
		ArrayList<String> principalPermutations = new ArrayList<String>();
		principalPermutations.add("x"); principalPermutations.add("y");
		
		ArrayList<ArrayList<String>> sortedUFG = InterchangeableUtils.calculateUFGFromComparisons(comparisons, functionName, principalPermutations);
		
		for (ArrayList<String> sort : sortedUFG) {
			for (String s : sort) {
				System.out.print(s + " ");
			}
			System.out.println();
		}
		
		ArrayList<String> programs = new ArrayList<String>();
		programs.add("(ite (and true (>= x y)) x y)");
		programs.add("4");
		
		programs = InterchangeableUtils.filterToInterchangeableProgramsWithUFG(programs, sortedUFG);
		System.out.println("After filter");
		for (String s : programs) {
			System.out.println(s);
		}
		
		/*
		String benchmarkFile = "src/main/resources/benchmarks/eqExample.sl";
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
		String functionName = benchmark.getFunctionName();
		
		String replacementToken = "(replacement_token ";
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			replacementToken += " " + benchmark.getVariableNames()[i];
		}
		replacementToken += ")";
		
		
		String originalAssertionString  = benchmark.getAssertionString();
		
		System.out.println("Original: " + originalAssertionString);
		
		
		String masterAssertionString = originalAssertionString;
		while(!InterchangeableUtils.checkAllMICompsFalse(functionName, masterAssertionString)) {
			
			ArrayList<String> compStore = new ArrayList<String>();
			
			masterAssertionString = InterchangeableUtils.blockOutNextConjunction(masterAssertionString, replacementToken, functionName, compStore, benchmark);
			
			System.out.println("Master Edited: " + masterAssertionString);
			
			String checkingAssertionString = masterAssertionString;
			masterAssertionString = InterchangeableUtils.replaceReplacementTokensWithFalse(masterAssertionString, compStore.size());
	
			
			System.out.println("Master Edited with falses: " + masterAssertionString);
			
			
			
			for (int i = 0; i < compStore.size(); i++) {
				System.out.println("Stored comp " + i + ": " + compStore.get(i));
			}
			
			checkingAssertionString = InterchangeableUtils.makeAllMICompsFalse(functionName, checkingAssertionString);
			checkingAssertionString = InterchangeableUtils.replaceReplacementTokens(checkingAssertionString, compStore);
			
			System.out.println("Checking Assertion String: " + checkingAssertionString);
			
			
		
			
			
		}
			*/
			
			
		
		
		/*
		
		String mockAssertionString = "(or (and (replacement_token x y) (= (f x y) 7)) (and (= (f x y) (f y x)) (= (f x y) 8)))";
		
		System.out.println(replaceReplacementTokensWithFalse(mockAssertionString, 1));
		
		ArrayList<String> storedComparisons  = new ArrayList<>();
		storedComparisons.add("(= (f x y) (f y x))");
		String check = 
		replaceReplacementTokens(mockAssertionString, storedComparisons);
		System.out.println(makeAllMICompsFalse(functionName, check));
		
		*/
		
		
		
	
		//String[] check = {"x", "y", "z"};
		/*
		ArrayList<String> check = new ArrayList<>();
		check.add("x"); check.add("y"); check.add("z");		

	
		
		ArrayList<String> permOne = new ArrayList<>();
		permOne.add("z"); permOne.add("y"); permOne.add("x"); permOne.add("r"); permOne.add("s");
		
		ArrayList<String> permTwo = new ArrayList<>();
		permTwo.add("y"); permTwo.add("x"); permTwo.add("z"); permTwo.add("s"); permTwo.add("r");
		
		System.out.println("ufvPairs");
		ArrayList<ArrayList<String>> ufvPairs = calculateUniqueUnfixedPairs(permOne, permTwo);
		
		for (ArrayList<String> ufvPair : ufvPairs) {
			
			for (String s : ufvPair) {
				System.out.print(s + " ");
			}
			System.out.println();
		}
		
		ArrayList<String> checker = new ArrayList<>();
		checker.add("r"); checker.add("s");
		
		System.out.println(sharesCommonVariables(ufvPairs.get(0), checker));
		
		
		ArrayList<ArrayList<String>> helper = new ArrayList<>();
		helper.add(permTwo);
		ArrayList<ArrayList<String>> UFG = calculateUnfixedGroups(permOne, helper);
		System.out.println("Unfixed Groups");
		
		UFG = sortUFGByLexicographicOrder(UFG);
		
		ArrayList<ArrayList<String>> UFGPerms = new ArrayList<>();
		for (ArrayList<String> g : UFG) {
			
			ArrayList<String> permutationsOfGroup = new ArrayList<>();
			constructPermutationFromArray(g.size(), g, " ", permutationsOfGroup);
			UFGPerms.add(permutationsOfGroup);		
		}
		
		ArrayList<ArrayList<String>> expandedUFGPerms =
		expandedUFGPermsAsLists(
		expandUFGPerms("", UFGPerms));
		
		String prog = "(+ (+ (* 2 x) (* 3 y)) (* 4 r))";
		
		System.out.println("Rock and roll hoochie coo");
		System.out.println(InterchangeableUtils.realizeInterchangeableProgram(prog, UFG, expandedUFGPerms));
		

		for (ArrayList<String> perm : expandedUFGPerms) {
			for (String s : perm) {
				System.out.print(s);
			}
			System.out.println();
		}

		
		System.out.println("Let's do some swapping");
		
		String program = "(ite (>= x y) x y)";
		
		System.out.println("Original: " + program);
		
		
		System.out.println("Swapped: " + swapVariables(expandedUFGPerms.get(0), expandedUFGPerms.get(1), program));
		
		ArrayList<String> checkPrograms = new ArrayList<>();
		checkPrograms.add("(- (+ z y) x)");
		checkPrograms.add("(- (+ z x) y)");
		
		ArrayList<String> principalPermutation = new ArrayList<>();
		principalPermutation.add("x"); principalPermutation.add("y"); principalPermutation.add("z");
		

		
		ArrayList<String> fixedVariables = InterchangeableUtils.calculateFixedVariablesFromPrograms(principalPermutation, checkPrograms);
		
		System.out.println("Fixed variables are below");
		
		for (String s : fixedVariables) {
			System.out.println(s);
		}
		
		
		
		System.out.println("Old UFG");
		
		for (ArrayList<String> l : UFG) {
			for (String s : l) {
				System.out.print(s + " ");
			}
			System.out.println();
		}
		
		InterchangeableUtils.removeFixedVariablesFromGroup(fixedVariables, UFG);
		
		System.out.println("New UFG");
		
		for (ArrayList<String> l : UFG) {
			for (String s : l) {
				System.out.print(s + " ");
			}
			System.out.println();
		}
		//System.out.println("Hello World!");*/
		
	}
	
	
}
