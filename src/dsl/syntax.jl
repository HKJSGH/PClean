using MacroTools

# There are various places in a PClean model where a Julia expression may
# occur. For each Julia expression, we must resolve it to either:
#    * A "name": another local variable (or ClassID), or a dot-expression picking out a variable in another class via a reference slot.
#    * A function, taking in values for the names involved in returning something.
# NOTE: The logic here does not treat reference slots as values. So, we cannot write
#    y ~ SomeClass
#    z ~ SomeClass
#    x = (some_condition) ? y : z
#    a ~ AddTypos(x.a)
# because the only way to refer to the attribute SomeClass.a is by directly using the 
# reference slot variables y or z (y.a or z.a).


"""
    strip_dots(expr)

If expr is a dot expression, remove everything after the dot. 
strip_dots()函数会移除点表达式在 . 后面的所有内容
"""
function strip_dots(expr)
    if expr isa Expr && expr.head == :.
        return strip_dots(expr.args[1]) # 递归调用strip_dots()函数，初始时把表达式可成 a . b,吗，每次检查 a 是否是 “ a . b ”的形式
    end
    return expr
end

"""
    parse_compound_expression(var_names::Set{Symbol}, fk_names::Set{Symbol}, expr)

Resolves `expr` to return three things:
* a list of all PClean names (locals or dot-expressions beginning w/ a reference slot)
  used by expr
* a list of symbols, of the same length as the list of PClean names, used by the modified
  expression.
* a modified expression that uses a single symbol in the place of any PClean name.  

解析' expr '返回三样东西:
*所有PClean名称的列表(局部变量或以引用槽开头的点表达式)
使用expr
*被修改者使用的与PClean名称列表相同长度的符号列表
表达式。
一个修改的表达式，在任何PClean名称的位置使用一个符号。

"""
function parse_compound_expression(var_names::Set{Symbol}, fk_names::Set{Symbol}, expr) # 定义域是符号的集合
    # A local variable 一个局部变量
    if expr isa Symbol && in(expr, var_names)
        return [expr], [expr], esc(expr)
    end
  
    # A dot expression       一个 . 表达式
    if expr isa Expr && expr.head == :. && in(strip_dots(expr), fk_names)
        return [expr], [Symbol(expr)], esc(Symbol(expr))
    end
  
    # A symbol meant to refer to some outside constant     一个代表外部变量的符号
    if expr isa Symbol
        return [], Symbol[], esc(expr)
    end
  
    # A literal or other non-expression type          文字或者其他非表达式类型
    if !(expr isa Expr)
        return [], Symbol[], expr
    end
    
    # Otherwise, it's a compound expression that we need to process recursively. 
    # 否则，它是我们需要递归处理的复合表达式，下文是递归调用的语句
    # 从中我们也可以看出，return的依次是pclean_names，used_symbols，new_expression。
    recursive_calls = [parse_compound_expression(var_names, fk_names, a) for a in expr.args]
    pclean_names = unique(vcat([result[1] for result in recursive_calls]...))
    used_symbols = unique(vcat([result[2] for result in recursive_calls]...))
    new_expression = Expr(expr.head, [result[3] for result in recursive_calls]...)
    return pclean_names, used_symbols, new_expression
end


"""
    parse_expression(var_names, fk_names, expr)

Returns either the expression itself (if it is already a PClean name), or
  * a list of PClean names
  * a list of Julia names
  * an expression that uses the Julia names for the values indicated by the PClean names
    
   返回表达式本身(如果它已经是一个PClean名称)，或者
  *一个PClean名称列表
  julia名字的列表 
  一个使用Julia名称来表示PClean名称所指示的值的表达式
    
"""
function parse_expression(var_names::Set{Symbol}, fk_names::Set{Symbol}, expr)
    if expr isa Symbol && in(expr, var_names)
        return expr
    end
    if expr isa Expr && expr.head == :. && in(strip_dots(expr), fk_names)
        return expr
    end
  
    # Otherwise, we have a function.
    return parse_compound_expression(var_names, fk_names, expr)
end
  

# Helper function that replaces block expressions with 
# literal :begin and :end lines, and brings all lines inside
# blocks to the top level.
    
# 用于将 block表达式 替换为 文字 “：begin ” 和 “：end ” 行 的辅助函数
# 并将 block 内的所有行带到顶层。
    
function flatten_lines(lines)
    flatlines = []
    for line in lines
        if line.head == :block
            push!(flatlines, :begin)
            push!(flatlines, flatten_lines(line.args)...)
            push!(flatlines, :end)
        else
            push!(flatlines, line)
        end
    end
    return flatlines
end

macro model(model_name, class_defs)
    class_defs = MacroTools.striplines(class_defs).args
    build_commands = Expr[]
    # For each class
    for class_def in class_defs
        MacroTools.@capture(class_def, @class classname_ body_)
        lines = flatten_lines(body.args)

        names = Set{Symbol}()
        fknames = Set{Symbol}()

        push!(build_commands, :(add_new_class!(builder, $(Meta.quot(classname)))))

        # For each line
        for line in lines
            if line == :begin
                push!(build_commands, :(begin_block!(builder, $(Meta.quot(classname)))))
            elseif line == :end
                push!(build_commands, :(end_block!(builder)))
            elseif @capture(line, lhs_Symbol = rhs_)
                names_for_lookup, syms, func_body = parse_compound_expression(names, fknames, rhs)
                push!(build_commands, :(add_julia_node!(builder, $(Meta.quot(classname)), $(Meta.quot(lhs)), $names_for_lookup, ($(map(esc, syms)...),) -> $(func_body))))
                push!(names, lhs)
            elseif @capture(line, lhs_Symbol ~ rhs_Symbol)
                push!(build_commands, :(add_foreign_key!(builder, $(Meta.quot(classname)), $(Meta.quot(lhs)), $(Meta.quot(rhs)))))
                push!(fknames, lhs)
            elseif @capture(line, lhs_Symbol ~ choice_Symbol(args__))
                processed_arguments = [parse_expression(names, fknames, arg) for arg in args]
                processed_arguments = [arg isa Tuple ? :(($(arg[1]), ($(map(esc, arg[2])...),) -> $(arg[3]))) : Expr(:quote, arg) for arg in processed_arguments]
                push!(build_commands, :(add_choice_node!(builder, $(Meta.quot(classname)), $(Meta.quot(lhs)), $(choice)(), [$(processed_arguments...)])))
                push!(names, lhs)
            elseif @capture(line, @guaranteed name_)
                push!(build_commands, :(add_guaranteed!(builder, $(Meta.quot(classname)), $(Meta.quot(name)))))
            elseif @capture(line, @learned name_::Dict{type1_, type_{params__}})
                push!(build_commands, :(add_indexed_parameter!(builder, $(Meta.quot(classname)), $(Meta.quot(name)), $type, $(params...))))
                push!(names, name)
            elseif @capture(line, @learned name_::Dict{type1_, type_})
                push!(build_commands, :(add_indexed_parameter!(builder, $(Meta.quot(classname)), $(Meta.quot(name)), $type)))
                push!(names, name)
            elseif @capture(line, @learned name_::type_{params__})
                push!(build_commands, :(add_basic_parameter!(builder,$(Meta.quot(classname)),  $(Meta.quot(name)), $type, $(params...))))
                push!(names, name)
            elseif @capture(line, @learned name_::type_)
                push!(build_commands, :(add_basic_parameter!(builder, $(Meta.quot(classname)), $(Meta.quot(name)), $type)))
                push!(names, name)
            end
        end

        push!(build_commands, :(finish_class!(builder, $(Meta.quot(classname)))))
    end
    quote 
        builder = PCleanModelBuilder(PCleanModel(Dict(), ClassID[]), closed)
        $(build_commands...)
        $(esc(model_name)) = finish_model!(builder)
    end
end

