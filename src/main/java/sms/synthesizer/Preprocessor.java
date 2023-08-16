package sms.synthesizer;

import java.util.ArrayList;
import java.util.HashSet;

import sms.benchmark.Benchmark;
import sms.multipleInvocation.MIUtils;
import sms.programNode.Node;

public class Preprocessor {
	
public static String[] extractSubprograms(Benchmark benchmark) {
		


		String assertionString = benchmark.getAssertionString();
		
		
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
		


		String assertionString = benchmark.getAssertionString();
		
		
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
				}
			} else {
				for (int i = 0; i < n.children.length; i++) {
					nodes.add(n.children[i]);
				}
			}
		}

		return MIUtils.transformProgramFromTempVarsToInvocation(constraintsAsProg.makeLispTree(), assigningInvocation);
	}

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
		////System.out.println("val prog 3 "  + valProg);
		Node[] replacements = new Node[2];
		replacements[0] = Node.buildNodeFromProgramString(replacementFunction, definedFunctionsSet);
		replacements[1] = Node.buildNodeFromProgramString(valProg, definedFunctionsSet);
		return replacements;
	}
 
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
