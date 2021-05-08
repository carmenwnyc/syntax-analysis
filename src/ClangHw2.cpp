//
// Template originally provided by Saikat Chakraborty on 9/24/2020.
// Functions isRecursiveFunction() and formatFunctionCalls() written by Carmen Wu
//

#include "hw2_util.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Lex/Lexer.h"
#include "clang/StaticAnalyzer/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>

#include <stack>
#include <string>
#include<string.h>

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace llvm;

static cl::OptionCategory FindFunctionCategory("");

class FunctionVisitor : public RecursiveASTVisitor<FunctionVisitor> {
public:
    explicit FunctionVisitor(ASTContext *_context, CompilerInstance &_compiler)
            : context(_context), compiler(_compiler) {}

    int getLineNumber(Stmt *stmt) {
        FullSourceLoc fullSourceLoc = context->getFullLoc(stmt->getBeginLoc());
        int ln;
        if (!fullSourceLoc.isValid())
            ln = -1;
        else
            ln = fullSourceLoc.getSpellingLineNumber();
        return ln;
    }

    std::string getSource(Stmt *node) {
        bool invalid;
        CharSourceRange range =
                CharSourceRange::getTokenRange(node->getBeginLoc(), node->getEndLoc());
        std::string tokens(Lexer::getSourceText(range, compiler.getSourceManager(),
                                                compiler.getLangOpts(), &invalid));
        if (!invalid) {
            return tokens;
        } else {
            return "";
        }
    }

    bool isRecursiveFunction(FunctionDecl *function, Stmt *stmt) {
        // Author: Carmen Wu

        std::string functionName = function->getNameInfo().getName().getAsString();

        //DFS to traverse down the AST
        std::stack<Stmt *> stack;
        stack.push(stmt);
        while(!stack.empty())
        {
            Stmt *node = stack.top();
            stack.pop();
            if (isa<CallExpr>(node)) //shouldn't it be isa<CallExpr *>(node) ? since node is a stmt pointer and CallExpr is child of Stmt
            {
                CallExpr *expr = dyn_cast<CallExpr>(node);
                // const FunctionDecl *getDirectCallee() const {
                // return dyn_cast_or_null<FunctionDecl>(getCalleeDecl());}
                //source: https://clang.llvm.org/doxygen/Expr_8h_source.html#l02904
                //If the callee is a FunctionDecl, return it FunctionDel *. Otherwise return null pointer.
                FunctionDecl *calleeFunc = expr->getDirectCallee();
                if (calleeFunc!=nullptr)
                {
                    //std::string calleeFuncName = calleeFunc->getNameInfo().getName().getAsString();
                    if (function == calleeFunc)
                    {
                        return true;
                    }
                }
            } else {
                for (auto child : node->children())
                {
                    if (child != nullptr)
                    {
                        stack.push(child);
                    }
                }
            }
        }//end of while loop
        return false;
    }


    std::string formatFunctionCall(CallExpr *callExpr) {
        std::string formattedExpr = "";
        // Author: Warmen Wu
        assert(isa<CallExpr>(callExpr)); //abort program if callExpr is not CallExpr

        Expr *callee = callExpr->getCallee();
        //Expr *    getCallee ()
        if (!isa<CallExpr>(callee))
        {
            formattedExpr += getSource(callee);
        }else{
            formatFunctionCall(callee);
        }

        formattedExpr += "(";
        int numArgs = callExpr->getNumArgs();
        int count = 0;
        //unsigned  getNumArgs () const
        //getNumArgs - Return the number of actual arguments to the call expression

        for (auto arg = callExpr->arg_begin(); arg != callExpr->arg_end(); ++arg)
        {   
            count++;
            if (!isa<CallExpr>(*arg))
            {
                formattedExpr += getSource(*arg);
                if (count < numArgs)
                {
                    formattedExpr += ",";
            }else{
                auto *node->*arg;
                CallExpr *arg_CallExpr = dyn_cast<CallExpr>(node);
                formatFunctionCall(arg_CallExpr);
            }
        }
        formattedExpr += ")";
        return formattedExpr;
    }

    void analyzeCallExpressionReformat(Stmt *root) {
        // We are doing a DFS on the input AST.
        // Whenever we find an AST node of type "CallExpr",
        // We reformat corresponding sub-tree.

        std::stack<Stmt *> stack;
        stack.push(root);
        while (!stack.empty()) {
            Stmt *node = stack.top();
            stack.pop();
            if (isa<CallExpr>(node)) {
                // This node is "CallExpr" Node, we need to reformat this.
                CallExpr *expr = dyn_cast<CallExpr>(node);

                int lineNo = getLineNumber(node);
                std::string originalSource = getSource(node);
                std::string reformattedSource = formatFunctionCall(expr);

                // The following line is the output of the reformatted call expression;
                printCallExprReformatOutput(lineNo, originalSource, reformattedSource);
            } else {
                // Since current node is not a CallExpr, let's visit the children.
                for (auto child : node->children()) {
                    if (child != nullptr) {
                        // We only want to visit the children which are not null.
                        stack.push(child);
                    }
                }
            }
        }
    }

    bool VisitFunctionDecl(FunctionDecl *function) {
        std::string functionName = function->getNameInfo().getName().getAsString();

        std::cout << "function name is : " << functionName <<'\n';

        if (!function->hasBody()) {
            // If the function does not have any body, we will not analyze it.
            return false;
        }
        Stmt *body = function->getBody();

        // Task 1
        bool recursive = isRecursiveFunction(function, body);
        printRecursiveFunction(functionName, recursive);

        // Task 2
        analyzeCallExpressionReformat(body);
        return true;
    }

    /*
     * This function is called when the visitor encounters a For statement in the
     * AST.
     */
    bool VisitForStmt(ForStmt *forStmt) {
        // We will give them this code for a reference code.
        assert(isa<ForStmt>(forStmt));
        int ln = getLineNumber(forStmt);
        printForStmt(ln);
        return true;
    }

private:
    ASTContext *context;
    CompilerInstance &compiler;
}; //end of FunctionVisitor class

class FunctionVisitorConsumer : public clang::ASTConsumer {
public:
    explicit FunctionVisitorConsumer(ASTContext *context,
                                     CompilerInstance &compiler)
            : visitor(context, compiler) {}

    virtual void HandleTranslationUnit(clang::ASTContext &context) {
        visitor.TraverseDecl(context.getTranslationUnitDecl());
    }

private:
    FunctionVisitor visitor;
}; //end of FunctionVisotorConsumer

class FunctionVisitAction : public clang::ASTFrontendAction {
public:
    virtual std::unique_ptr<clang::ASTConsumer>
    CreateASTConsumer(clang::CompilerInstance &compiler, llvm::StringRef inFile) {
        return std::unique_ptr<clang::ASTConsumer>(
                new FunctionVisitorConsumer(&compiler.getASTContext(), compiler));
    }
};

int main(int argc, const char **argv) {
    CommonOptionsParser optionsParser(argc, argv, FindFunctionCategory);
    ClangTool tool(optionsParser.getCompilations(),
                   optionsParser.getSourcePathList());
    return tool.run(newFrontendActionFactory<FunctionVisitAction>().get());
}
