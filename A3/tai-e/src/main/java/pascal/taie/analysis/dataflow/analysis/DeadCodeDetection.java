/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // 可达Stmt集合reach
        Set<Stmt> reach = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // 遍历过的Stmt集合checked
        Set<Stmt> checked = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> stmts = new ArrayDeque<>();
        reach.add(cfg.getEntry());
        reach.add(cfg.getExit());
        stmts.add(cfg.getEntry());
        while (!stmts.isEmpty()) {
            Stmt stmt = stmts.poll();
            checked.add(stmt);
            if (stmt instanceof If){
                reach.add(stmt);
                Value condVal = ConstantPropagation.evaluate(((If) stmt).getCondition(), constants.getInFact(stmt));
                if (condVal.isConstant()){
                    if (condVal.getConstant() == 1){
                        // True
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                            if (edge.getKind() == Edge.Kind.IF_TRUE && !checked.contains(edge.getTarget())){
                                stmts.add(edge.getTarget());
                            }
                        }
                    }
                    else {
                        // False
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                            if (edge.getKind() == Edge.Kind.IF_FALSE && !checked.contains(edge.getTarget())){
                                stmts.add(edge.getTarget());
                            }
                        }
                    }
                }
                else{
                    for (Stmt succ : cfg.getSuccsOf(stmt)){
                        if (!checked.contains(succ)){
                            stmts.add(succ);
                        }
                    }
                }
            }
            else if (stmt instanceof AssignStmt) {
                reach.add(stmt);
                LValue lval = ((AssignStmt) stmt).getLValue();
                RValue rval = ((AssignStmt) stmt).getRValue();
                boolean dead = lval instanceof Var && !liveVars.getResult(stmt).contains((Var) lval) && hasNoSideEffect(rval);
                if (dead){
                    // 添加无用赋值到死代码集合中
                    deadCode.add((Stmt) stmt);
                }
                for (Stmt succ : cfg.getSuccsOf(stmt)){
                    if (!checked.contains(succ)){
                        stmts.add(succ);
                    }
                }
            }
            else if (stmt instanceof SwitchStmt) {
                reach.add(stmt);
                Value caseVal = constants.getResult(stmt).get(((SwitchStmt) stmt).getVar());
                if (caseVal.isConstant()){
                    int i = ((SwitchStmt) stmt).getCaseValues().indexOf(caseVal.getConstant());
                    if (i != -1){
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                            if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == caseVal.getConstant() && !checked.contains(edge.getTarget())){
                                stmts.add(edge.getTarget());
                            }
                        }
                    }
                    else {
                        Stmt dfstmt = ((SwitchStmt) stmt).getDefaultTarget();
                        if (!checked.contains(dfstmt)){
                            stmts.add(dfstmt);
                        }
                    }
                }
                else {
                    for (Stmt succ : cfg.getSuccsOf(stmt)) {
                        if (!checked.contains(succ)) {
                            stmts.add(succ);
                        }
                    }
                }
            }
            else {
                reach.add(stmt);
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!checked.contains(succ)) {
                        stmts.add(succ);
                    }
                }
            }
        }
        // 添加不可达代码到死代码集合中
        for (Stmt stmt: ir){
            if (!reach.contains(stmt)){
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
