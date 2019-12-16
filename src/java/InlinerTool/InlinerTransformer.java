package InlinerTool;

import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.PackManager;
import soot.PatchingChain;
import soot.PrimType;
import soot.PhaseOptions;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.ShortType;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.SootClass;
import soot.Transform;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NeExpr;
import soot.jimple.NopStmt;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.invoke.InlinerSafetyManager;
import soot.jimple.toolkits.invoke.SiteInliner;
import soot.options.Options;
import soot.tagkit.Tag;
import soot.tagkit.BytecodeOffsetTag;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.lang.RuntimeException;
import java.lang.StringBuilder;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class InlinerTransformer extends SceneTransformer {

	private HashMap<String, HashMap<Integer, List<String>>> inlineTargets = new HashMap<>();
	private HashMap<String, SootMethod> methodMap = new HashMap<>();

	public InlinerTransformer(String inlineTargetsPath) throws IOException {
		FileReader fileReader = new FileReader(inlineTargetsPath);
		BufferedReader bufferedReader = new BufferedReader(fileReader);
		String line = null;
		while ((line = bufferedReader.readLine()) != null) {
			String[] lineSplit = line.split(" ");
			String callsiteSignature = lineSplit[0];
			String calleeHotSpotSignature = lineSplit[1];

			String[] callsiteSignatureSplit =
				callsiteSignature.split("@");
			String callerHotSpotSignature =
				callsiteSignatureSplit[0];
			Integer callsiteBytecodeOffset =
				Integer.valueOf(callsiteSignatureSplit[1]);

			if (!inlineTargets.containsKey(callerHotSpotSignature)) {
				inlineTargets.put(callerHotSpotSignature, new HashMap<>());
			}

			HashMap<Integer, List<String>> methodCallsites =
				inlineTargets.get(callerHotSpotSignature);
			List<String> callsiteList =
				methodCallsites.get(callsiteBytecodeOffset);

			if (callsiteList == null) {
				callsiteList = new ArrayList<String>();
				callsiteList.add(calleeHotSpotSignature);
				methodCallsites.put(callsiteBytecodeOffset, callsiteList);
			} else {
				callsiteList.add(calleeHotSpotSignature);
			}
		}
	}

	// https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.2
	private void buildFieldDescriptor(StringBuilder sb, Type type) {
		if (type instanceof RefType) {
			RefType refType = (RefType) type;
			String sootClassName = refType.getClassName();
			sb.append('L');
			sb.append(sootClassName.replace('.', '/'));
			sb.append(';');
		}
		else if (type instanceof ArrayType) {
			ArrayType arrayType = (ArrayType) type;
			sb.append('[');
			buildFieldDescriptor(sb, arrayType.baseType);
		}
		else if (type instanceof BooleanType) {
			sb.append('Z');
		}
		else if (type instanceof ByteType) {
			sb.append('B');
		}
		else if (type instanceof CharType) {
			sb.append('C');
		}
		else if (type instanceof DoubleType) {
			sb.append('D');
		}
		else if (type instanceof FloatType) {
			sb.append('F');
		}
		else if (type instanceof IntType) {
			sb.append('I');
		}
		else if (type instanceof LongType) {
			sb.append('J');
		}
		else if (type instanceof ShortType) {
			sb.append('S');
		}
		else {
			throw new RuntimeException(
				"Unhandled Type: " + type.getClass().getName());
		}
	}

	private String getHotSpotSignature(SootMethod sootMethod) {
		SootClass sootClass = sootMethod.getDeclaringClass();
		StringBuilder sb = new StringBuilder();
		sb.append(sootClass.getName().replace('.', '/'));
		sb.append('.');
		sb.append(sootMethod.getName());
		sb.append('(');
		boolean firstParameter = true;
		for (Type parameterType : sootMethod.getParameterTypes()) {
			if (firstParameter) { firstParameter = false; }
			else                { sb.append(','); }

			if (parameterType instanceof RefType) {
				RefType refType = (RefType) parameterType;
				String sootClassName = refType.getClassName();
				sb.append(sootClassName.replace('.', '/'));
			}
			else if (parameterType instanceof PrimType) {
				PrimType primType = (PrimType) parameterType;
				sb.append(primType.toString());
			}
			else if (parameterType instanceof ArrayType) {
				buildFieldDescriptor(sb, parameterType);
			}
			else {
				throw new RuntimeException(
					"Unhandled Parameter Type: "
					+ parameterType.getClass().getName());
			}
		}
		sb.append(')');
		return sb.toString();
	}

	@Override
	public void internalTransform(String phaseName, Map options) {
		for (SootClass sootClass : Scene.v().getClasses()) {
			try{
			for (SootMethod sootMethod : sootClass.getMethods()) {
				if (!sootMethod.isConcrete()) {
					continue;
				}
				String hotSpotSignature =
					getHotSpotSignature(sootMethod);
				methodMap.put(hotSpotSignature, sootMethod);
			}
			}catch(Exception e){continue;}
		}

		int count = 0;
		for (Map.Entry<String, HashMap<Integer, List<String>>> entry
		     : inlineTargets.entrySet()) {
			String callerHotSpotSignature = entry.getKey();
			HashMap<Integer, List<String>> bytecodeOffsetCalleeMap =
				entry.getValue();

			if (!methodMap.containsKey(callerHotSpotSignature)) {
				continue;
			}

			SootMethod sootCaller = methodMap.get(
				callerHotSpotSignature);
			handleInline(sootCaller, bytecodeOffsetCalleeMap);
		}
	}

	private void handleInline(SootMethod sootCaller,
	                          HashMap<Integer, List<String>> bytecodeOffsetCalleeMap) {
		Body body = sootCaller.retrieveActiveBody();

		// The bytecode offsets could be wrong (there are bugs in ASM)
		// This block of code checks that the offsets actually line up,
		// if not we skip this method
		HashMap<Integer, SootMethod> bytecodeOffsetFoundMap = new HashMap<>();
		for (Unit u : body.getUnits()) {
			Stmt stmt = (Stmt) u;
			if (!stmt.containsInvokeExpr()) {
				continue;
			}
			InvokeExpr invokeExpr = stmt.getInvokeExpr();
			BytecodeOffsetTag bytecodeOffsetTag =
				(BytecodeOffsetTag)
				stmt.getTag("BytecodeOffsetTag");
			if (bytecodeOffsetTag == null) {
				continue;
			}
			int bytecodeOffset = bytecodeOffsetTag.getBytecodeOffset();
			Integer bytecodeOffsetKey = Integer.valueOf(bytecodeOffset);
			bytecodeOffsetFoundMap.put(bytecodeOffsetKey, invokeExpr.getMethod());
		}
		String callerSignature = getHotSpotSignature(sootCaller);
		boolean match = true;
		for (Integer bytecodeOffsetKey : bytecodeOffsetCalleeMap.keySet()) {
			if (!bytecodeOffsetFoundMap.containsKey(bytecodeOffsetKey)) {
				match = false;
				break;
			}
			SootMethod foundSootCallee = bytecodeOffsetFoundMap.get(bytecodeOffsetKey);
			List<String> targetList = bytecodeOffsetCalleeMap.get(bytecodeOffsetKey);

			if (targetList.size() > 2) {
				return;
			}

			for (String calleeHotSpotSignature : targetList) {
				if (!methodMap.containsKey(calleeHotSpotSignature)) {
					break;
				}

				SootMethod sootCallee = methodMap.get(calleeHotSpotSignature);
				if (!foundSootCallee.getName().equals(sootCallee.getName())) {
					match = false;
					break;
				}
			}
		}
		if (!match) {
			return;
		}

		Iterator unitsIter = body.getUnits().snapshotIterator();
		while (unitsIter.hasNext()) {
			Stmt stmt = (Stmt) unitsIter.next();

			if (!stmt.containsInvokeExpr()) {
				continue;
			}
			InvokeExpr invokeExpr = stmt.getInvokeExpr();

			BytecodeOffsetTag bytecodeOffsetTag =
				(BytecodeOffsetTag)
				stmt.getTag("BytecodeOffsetTag");
			if (bytecodeOffsetTag == null) {
				continue;
			}
			int bytecodeOffset = bytecodeOffsetTag.getBytecodeOffset();
			Integer bytecodeOffsetKey = Integer.valueOf(bytecodeOffset);
			if (!bytecodeOffsetCalleeMap.containsKey(bytecodeOffsetKey)) {
				continue;
			}

			List<String> targets = bytecodeOffsetCalleeMap.get(bytecodeOffsetKey);

			if (targets.size() > 2) {
				continue;
			} else if (targets.size() == 1) {
				handleSingleInline(targets.get(0), stmt, sootCaller);
			} else { // targets.size == 2
				handleDoubleInline(targets, stmt, sootCaller, body);
			}
		}
	}

	private void handleSingleInline(String calleeHotSpotSignature,
									Stmt stmt,
									SootMethod sootCaller) {
		if (!methodMap.containsKey(calleeHotSpotSignature)) {
		    return;
		}

		SootMethod sootCallee = methodMap.get(calleeHotSpotSignature);
		if (containsProtectedAbstractInvoke(sootCallee)) {
			return;
		}

		if (containsAbstractMethodError(sootCallee)) {
			return;
		}

		SootClass callerClass = sootCaller.getDeclaringClass();
		if (containsInterPackageProtectedInvoke(callerClass, sootCallee)) {
			return;
		}

		if (containsInterPackageProtectedAccess(callerClass, sootCallee)) {
			return;
		}

		boolean safeToInline =
			InlinerSafetyManager.ensureInlinability(
				sootCallee, stmt, sootCaller, "unsafe");
		if (!safeToInline) {
			return;
		}

		SiteInliner.inlineSite(sootCallee, stmt, sootCaller);
	}

	private void handleDoubleInline(List<String> targets,
									Stmt stmt,
									SootMethod sootCaller,
									Body body) {
		if (targets.size() != 2) {
			return;
		}

		InvokeExpr invokeExpr = stmt.getInvokeExpr();

		if (!(invokeExpr instanceof VirtualInvokeExpr)) {
			return;
		}

		boolean safe = true;
		for (String calleeHotSpotSignature : targets) {
			if (!methodMap.containsKey(calleeHotSpotSignature)) {
			    safe = false;
				break;
			}
			SootMethod sootCallee = methodMap.get(calleeHotSpotSignature);

			if (containsProtectedAbstractInvoke(sootCallee)) {
				safe = false;
				break;
			}

			if (containsAbstractMethodError(sootCallee)) {
				safe = false;
				break;
			}

			SootClass callerClass = sootCaller.getDeclaringClass();
			if (containsInterPackageProtectedInvoke(callerClass, sootCallee)) {
				safe = false;
				break;
			}

			if (containsInterPackageProtectedAccess(callerClass, sootCallee)) {
				safe = false;
				break;
			}

			boolean safeToInline =
				InlinerSafetyManager.ensureInlinability(
					sootCallee, stmt, sootCaller, "unsafe");

			if (!safeToInline) {
				safe = false;
				break;
			}
		}

		if (!safe) {
			return;
		}

		PatchingChain units = body.getUnits();

		String calleeHotspotSignatureA = targets.get(0);
		String calleeHotspotSignatureB = targets.get(1);
		SootMethod calleeA = methodMap.get(calleeHotspotSignatureA);
		SootMethod calleeB = methodMap.get(calleeHotspotSignatureB);
		SootClass classA = calleeA.getDeclaringClass();
		SootClass classB = calleeB.getDeclaringClass();
		String classAName = classA.getName().replace('.', '/');
		String classBName = classB.getName().replace('.', '/');

		VirtualInvokeExpr vInvokeExpr = (VirtualInvokeExpr) invokeExpr;
		Local base = (Local) vInvokeExpr.getBase();

		SootMethod getClass = getSootMethodOrNull(base.getType().toString(),
												  "getClass",
												  "java.lang.Class",
												  null);

		if (getClass == null) {
			// base was an interface
			return;
		}

		String[] forNameArgs = {"java.lang.String"};
		SootMethod forName = getSootMethod("java.lang.Class",
										   "forName",
											"java.lang.Class",
											Arrays.asList(forNameArgs));
		SootMethodRef getClassMethodref = getClass.makeRef();
		SootMethodRef forNameMethodRef = forName.makeRef();

		VirtualInvokeExpr typeInvokeExpr =
							Jimple.v().newVirtualInvokeExpr(base,
														    getClassMethodref);


		Local typeLocal = Jimple.v().newLocal("type",
											  getClass.getReturnType());
		Local typeA = Jimple.v().newLocal("typeA",
											   getClass.getReturnType());
		Local typeB = Jimple.v().newLocal("typeB",
											   getClass.getReturnType());
		body.getLocals().add(typeLocal);
		body.getLocals().add(typeA);
		body.getLocals().add(typeB);

		StringConstant typeAString = StringConstant.v(classAName);
		StringConstant typeBString = StringConstant.v(classBName);

		StaticInvokeExpr forClassAExpr =
							Jimple.v().newStaticInvokeExpr(forNameMethodRef,
														   typeAString);
		StaticInvokeExpr forClassBExpr =
							Jimple.v().newStaticInvokeExpr(forNameMethodRef,
														   typeBString);

		// type = receiver.getClass()
		// typeA = classA
		// typeB = classB
		// stmt
		// clonedstmt
		// done
		AssignStmt typeAssignment = Jimple.v().newAssignStmt(typeLocal,
															 typeInvokeExpr);
		AssignStmt typeAAssignment = Jimple.v().newAssignStmt(typeA,
															  forClassAExpr);
		AssignStmt typeBAssignment = Jimple.v().newAssignStmt(typeB,
															  forClassAExpr);
		Stmt clonedStmt = (Stmt) stmt.clone();
		units.insertAfter(clonedStmt, stmt);

		units.insertBefore(typeAssignment, stmt);
		units.insertAfter(typeAAssignment, typeAssignment);
		units.insertAfter(typeBAssignment, typeAAssignment);

		NopStmt done = Jimple.v().newNopStmt();
		units.insertAfter(done, clonedStmt);

		// if type != typeA goto l2
		//    inline typeA.foo
		//    goto done
		// l2:
		// if type != typeB goto done
		//    inline typeB.foo
        // done:
		NeExpr typeAComparison = Jimple.v().newNeExpr(typeLocal, typeA);
		NeExpr typeBComparison = Jimple.v().newNeExpr(typeLocal, typeB);

		IfStmt typeBIf = Jimple.v().newIfStmt(typeBComparison, done);
		IfStmt typeAIf = Jimple.v().newIfStmt(typeAComparison, typeBIf);
		units.insertBefore(typeAIf, stmt);
		units.insertBefore(typeBIf, clonedStmt);

		GotoStmt gotoDone = Jimple.v().newGotoStmt(done);
		units.insertAfter(gotoDone, stmt);

		SiteInliner.inlineSite(calleeA, stmt, sootCaller);
		SiteInliner.inlineSite(calleeB, clonedStmt, sootCaller);
	}

    private boolean containsProtectedAbstractInvoke(SootMethod method) {
		Body body = method.retrieveActiveBody();
		Iterator units = body.getUnits().iterator();
		while (units.hasNext()) {
			Stmt invokeStmt = (Stmt) units.next();
			if (!invokeStmt.containsInvokeExpr()) {
				continue;
			}

			InvokeExpr ie = invokeStmt.getInvokeExpr();
			if (ie.getMethod().isProtected() && ie.getMethod().isAbstract()) {
				return true;
			}
		}
		return false;
	}

	private boolean containsAbstractMethodError(SootMethod method) {
		for (SootClass e : method.getExceptions()) {
			if (e.getName().equals("java.lang.AbstractMethodError")) {
				return true;
			}
		}

		Body body = method.retrieveActiveBody();
		Iterator units = body.getUnits().iterator();
		while (units.hasNext()) {
			Stmt stmt = (Stmt) units.next();
			if (!(stmt instanceof ThrowStmt)) {
				continue;
			}

			ThrowStmt throwStmt = (ThrowStmt) stmt;
			Local local = (Local) throwStmt.getOp();
			String type = local.getType().toString();
			if (type.equals("java.lang.AbstractMethodError")) {
				return true;
			}
		}
		return false;
	}

	private boolean containsInterPackageProtectedInvoke(SootClass callerClass, SootMethod target) {
		Body body = target.retrieveActiveBody();
		Iterator units = body.getUnits().iterator();

		SootClass targetClass = target.getDeclaringClass();
		String callerPackage = callerClass.getPackageName();
		String targetPackage = targetClass.getPackageName();
		if (callerPackage.equals(targetPackage)) {
			return false;
		}

		// will inlining this target invoke a protected method
		// from another package?
		// go through every invoke statement to check
		while (units.hasNext()) {
			Stmt stmt = (Stmt) units.next();

			if (!stmt.containsInvokeExpr()) {
				continue;
			}

			InvokeExpr ie = stmt.getInvokeExpr();
			SootMethod targetMethod = ie.getMethod();
			if (targetMethod.isProtected()) {
				return true;
			}
		}
		return false;
	}

	private boolean containsInterPackageProtectedAccess(SootClass callerClass, SootMethod target) {
		Body body = target.retrieveActiveBody();
		Iterator units = body.getUnits().iterator();

		SootClass targetClass = target.getDeclaringClass();
		String callerPackage = callerClass.getPackageName();
		String targetPackage = targetClass.getPackageName();
		if (callerPackage.equals(targetPackage)) {
			return false;
		}

		while (units.hasNext()) {
			Stmt stmt = (Stmt) units.next();
			if (!(stmt instanceof AssignStmt)) {
				continue;
			}

			AssignStmt as = (AssignStmt)stmt;
			Value left = as.getLeftOp();
			Value right = as.getRightOp();

			if (left instanceof FieldRef) {
				SootField f = ((FieldRef)left).getField();
				if (f.isProtected()) {
					return true;
				}
			}

			if (right instanceof FieldRef) {
				SootField f = ((FieldRef)right).getField();
				if (f.isProtected()) {
					return true;
				}
			}
		}
		return false;
	}

	private SootMethod getSootMethod(String className,
									 String methodName,
									 String retType,
									 List<String> args) {
		String name = buildSootMethodString(className,
											methodName,
											retType,
											args);
		return Scene.v().getMethod(name);
	}

	private SootMethod getSootMethodOrNull(String className,
										   String methodName,
										   String retType,
										   List<String> args) {
		String name = buildSootMethodString(className,
											methodName,
											retType,
											args);

		if (!Scene.v().containsMethod(name)) {
			return null;
		}

		return Scene.v().getMethod(name);
	}

	private String buildSootMethodString(String className,
										 String methodName,
										 String retType,
										 List<String> args) {
		StringBuilder sb = new StringBuilder();
		sb.append("<");
		sb.append(className); // qualified.class.name
		sb.append(":");
		sb.append(retType); // return type
		sb.append(" ");
		sb.append(methodName); // methodName(P1, P2)
		sb.append("(");

		if (args != null) {
			for (int i = 0; i < args.size(); ++i) {
				String arg = args.get(i);
				sb.append(arg);

				if (i != args.size()-1) {
					sb.append(",");
				}
			}
		}

		sb.append(")");
		sb.append(">");

		return sb.toString();
	}
}
