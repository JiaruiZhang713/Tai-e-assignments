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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import ppg.parse.Constant;

import java.util.Objects;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpfact = new CPFact();
        for (Var var : cfg.getIR().getVars()){
            if (canHoldInt(var)){
                cpfact.update(var, Value.getNAC());
            }
        }
        return cpfact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()){
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            target.update(var, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        else if (v1.isUndef()) {
            return v2;
        }
        else if (v2.isUndef()) {
            return v1;
        }
        else if (v1.getConstant() == v2.getConstant()) {
            return v1;
        }
        else
            return Value.getNAC();
    }
//transferNode ：负责实现控制流图中结点的 transfer function 。如果 OUT 改变，返回 true ；否则返回 false 。
//stmt 表示结点中的一条中间表示，一个结点只有一个中间表示。
//
//题目要求只需要对赋值语句处理，所以用 DefinitionStmt 类型过滤。
//
//对于所有赋值语句，只考虑具有左值，并且左值是变量且类型可以转换成 int 的语句。这些语句的右值是一个表达式，可能是常量，也能是变量、二元表达式。这个右值表达式的值将通过 evaluate 函数计算。
//
//对于其他类型的语句，不做处理，out 直接复制 in 即可，相当于经过一个恒等函数。
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact in_new = in.copy();
        if (stmt instanceof DefinitionStmt) {
            if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var && canHoldInt((Var)stmt.getDef().get())){
                in_new.update((Var)stmt.getDef().get(), Objects.requireNonNull(evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in_new)));
            }
        }
        return out.copyFrom(in_new);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var){
            return in.get((Var) exp);
        }
        else if (exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp){
            Var o1 = ((BinaryExp) exp).getOperand1();
            Var o2 = ((BinaryExp) exp).getOperand2();
            Value v1 = in.get(o1);
            Value v2 = in.get(o2);
            if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
            else if (v1.isNAC() || v2.isNAC()) {
                if (v1.isNAC() && exp instanceof ArithmeticExp &&
                        ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV) {}
                return Value.getNAC();
            }

            if (exp instanceof ArithmeticExp) {
                switch (((ArithmeticExp) exp).getOperator()) {
                    case ADD:
                    case SUB:
                    case MUL:
                    case DIV:
                    case REM:
                }
            }
            else if (exp instanceof ConditionExp) {

            }
            else if  (exp instanceof BitwiseExp) {

            }

        }
        return Value.getNAC();
    }
}
