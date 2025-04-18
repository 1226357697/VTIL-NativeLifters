
#include <lifters/core>
#include <lifters/amd64>
#include <vtil/arch>
#include <vtil/compiler>


#include <ida.hpp>
#include <idp.hpp>
#include <loader.hpp>
#include <funcs.hpp>

#include <vector>
#include <memory>

using namespace vtil;
using namespace logger;

using amd64_recursive_descent = lifter::recursive_descent<lifter::byte_input, lifter::amd64::lifter_t>;
// Define the class that inherits from plugmod_t

static void dump(const instruction& ins, const instruction* prev = nullptr)
{
	using namespace logger;

	// Print stack pointer offset
	//
	if (ins.sp_index)
		msg("[%d] ", ins.sp_index);
	else
		msg("    ");

	if (ins.sp_reset)
		msg(">%c0x%-4x ", ins.sp_offset >= 0 ? '+' : '-', abs(ins.sp_offset));
	else if ((prev ? prev->sp_offset : 0) == ins.sp_offset)
		msg("%c0x%-4x  ", ins.sp_offset >= 0 ? '+' : '-', abs(ins.sp_offset));
	else if ((prev ? prev->sp_offset : 0) > ins.sp_offset)
		msg("%c0x%-4x  ", ins.sp_offset >= 0 ? '+' : '-', abs(ins.sp_offset));
	else
		msg("%c0x%-4x  ", ins.sp_offset >= 0 ? '+' : '-', abs(ins.sp_offset));

	// Print name
	//
	if (ins.is_volatile())
		msg(VTIL_FMT_INS_MNM " ", ins.base->to_string(ins.access_size()));			// Volatile instruction
	else
		msg(VTIL_FMT_INS_MNM " ", ins.base->to_string(ins.access_size()));			// Non-volatile instruction

	// Print each operand
	//
	for (auto& op : ins.operands)
	{
		if (op.is_register())
		{
			if (op.reg().is_stack_pointer())
				msg(VTIL_FMT_INS_OPR " ", op.reg());									// Stack pointer
			else if (op.reg().is_physical())
				msg(VTIL_FMT_INS_OPR " ", op.reg());									// Any hardware/special register
			else
				msg(VTIL_FMT_INS_OPR " ", op.reg());									// Virtual register
		}
		else
		{
			fassert(op.is_immediate());

			if (ins.base->memory_operand_index != -1 &&
				&ins.operands[size_t(ins.base->memory_operand_index) + 1] == &op &&
				ins.operands[ins.base->memory_operand_index].reg().is_stack_pointer())
			{
				if (op.imm().i64 >= 0)
					msg(VTIL_FMT_INS_OPR " ", format::hex(op.imm().i64));			 // External stack
				else
					msg(VTIL_FMT_INS_OPR " ", format::hex(op.imm().i64));			 // VM stack
			}
			else
			{
				msg(VTIL_FMT_INS_OPR " ", format::hex(op.imm().i64));				 // Any immediate
			}
		}
	}

	// End line
	//
	msg("\n");
}

static void dump(const basic_block* blk, std::set<const basic_block*>* visited = nullptr)
{
	using namespace vtil::logger;
	scope_padding _p(4);

	bool blk_visited = visited ? visited->contains(blk) : false;

	auto end_with_bool = [](bool b)
	{
		if (b) msg("Y\n");
		else msg("N\n");
	};

	msg("Entry point VIP:       ");
	msg("0x%llx\n", blk->entry_vip);
	msg("Stack pointer:         ");
	if (blk->sp_offset < 0)
		msg("%s\n", format::hex(blk->sp_offset));
	else
		msg("%s\n", format::hex(blk->sp_offset));
	msg("Already visited?:      ");
	end_with_bool(blk_visited);
	msg("------------------------\n");

	if (blk_visited)
		return;

	// Print each instruction
	//
	int ins_idx = 0;
	bool no_disasm = false;
	for (auto it = blk->begin(); !it.is_end(); ++it, ins_idx++)
	{
		// If vemit, try to disassmble if not done already.
		//
		if (it->base->name == "vemit")
		{
			if (!no_disasm)
			{
				std::vector<uint8_t> bytes;
				for (auto it2 = it; !it2.is_end(); it2++)
				{
					if (it2->base->name != "vemit")
						break;
					uint8_t* bs = (uint8_t*)&it2->operands[0].imm().u64;
					bytes.insert(bytes.end(), bs, bs + it2->operands[0].size());
				}

				if (bytes.size())
				{
					if (it.block->owner->arch_id == architecture_amd64)
					{
						auto dasm = amd64::disasm(bytes.data(), it->vip == invalid_vip ? 0 : it->vip, bytes.size());
						for (auto& ins : dasm)
							msg("; %s\n", ins);
					}
					else
					{
						auto dasm = arm64::disasm(bytes.data(), it->vip == invalid_vip ? 0 : it->vip, bytes.size());
						for (auto& ins : dasm)
							msg("; %s\n", ins);
					}
				}
				no_disasm = true;
			}
		}
		else
		{
			no_disasm = false;
		}

		// Print string context if any.
		//
		if (it->context.has<std::string>())
		{
			const std::string& cmt = it->context;
			msg("// %s\n", cmt);

			// Skip if nop.
			//
			if (it->base == &ins::nop) continue;
		}

		msg("%04d: ", ins_idx);
		if (it->vip == invalid_vip)
			msg("[ PSEUDO ] ");
		else
			msg("[%08x] ", (uint32_t)it->vip);
		dump(*it, it.is_begin() ? nullptr : &*std::prev(it));
	}

	// Dump each branch as well
	//
	if (visited)
	{
		visited->insert(blk);
		for (auto& child : blk->next)
			dump(child, visited);
	}
}

void dump(const routine* routine)
{
	std::set<const basic_block*> vs;
	dump(routine->entry_point, &vs);
}

class  optimization_handler : public action_handler_t
{
	// Inherited via action_handler_t
	int idaapi activate(action_activation_ctx_t* ctx) override
	{
		msg("MyPlugmod: Action activated.\n");
		ea_t ea1, ea2;
		if (read_range_selection(nullptr, &ea1, &ea2)) // the selection is present?
		{
			msg("ea1:%llx ea2:%llx.\n", ea1, ea2);
		}

		std::vector<uint8_t>code;
		code.resize(ea2 -ea1);
		code.resize(get_bytes(code.data(), code.size(), ea1));
    

		lifter::byte_input input = { code.data(), code.size() };

		auto dasm = amd64::disasm(code.data(), 0, code.size());
		for (auto& ins : dasm)
			msg("%s\n", ins.to_string());

		amd64_recursive_descent rec_desc(&input, 0);
		rec_desc.entry->owner->routine_convention = amd64::default_call_convention;
		rec_desc.entry->owner->routine_convention.purge_stack = false;
		rec_desc.explore();

		optimizer::apply_all_profiled(rec_desc.entry->owner);
		//debug::dump(rec_desc.entry->owner);
		dump(rec_desc.entry->owner);

		return true;
	}
	action_state_t idaapi update(action_update_ctx_t* ctx) override
	{
		return AST_ENABLE_ALWAYS;
	}
};

static optimization_handler opt_handler;




class Vtilplugmod : public plugmod_t
{
public:
	//---------------------------------------------------------------------------
	// Callback for ui notifications
	static ssize_t idaapi ui_callback(void* ud, int notification_code, va_list va)
	{
		switch (notification_code)
		{
			// called when IDA is preparing a context menu for a view
			// Here dynamic context-depending user menu items can be added.
		case ui_populating_widget_popup:
		{
			TWidget* view = va_arg(va, TWidget*);
			if (get_widget_type(view) == BWN_DISASM)
			{
				TPopupMenu* p = va_arg(va, TPopupMenu*);
				Vtilplugmod* plgmod = (Vtilplugmod*)ud;
				attach_action_to_popup(view, p, "Vtil:optimization");
			}
		}
		break;
		}
		return 0;
	}

	// Constructor
	Vtilplugmod()
	{
		msg("MyPlugmod: Constructor called.\n");
		// Register actions
		const action_desc_t actions[] =
		{
	#define ROW(name, label, handler) ACTION_DESC_LITERAL_PLUGMOD(name, label, handler, this, nullptr, nullptr, -1)
			ROW("Vtil:optimization", "lifter vtil and optimization", &opt_handler),
	#undef ROW
		};

		for (size_t i = 0, n = qnumber(actions); i < n; ++i)
			register_action(actions[i]);

		hook_to_notification_point(HT_UI, ui_callback, this);
	}

	// Destructor
	virtual ~Vtilplugmod()
	{
		msg("MyPlugmod: Destructor called.\n");
		unregister_action("Vtil:optimization");
	}

	// Method that gets called when the plugin is activated
	virtual bool idaapi run(size_t arg) override
	{
		msg("MyPlugmod.run() called with arg: %d\n", arg);

		// Iterate through all functions and print their names and addresses
		int n = get_func_qty();
		for (int i = 0; i < n; i++) {
			func_t* pfn = getn_func(i);
			if (pfn == nullptr)
				continue;

			qstring name;
			get_func_name(&name, pfn->start_ea);
			msg("Function %s at address 0x%llX\n", name.length() ? name.c_str() : "-UNK-", pfn->start_ea);
		}

		return true;
	}
};

static plugmod_t* idaapi init(void)
{
  return new Vtilplugmod();
}
plugin_t PLUGIN =
{
  IDP_INTERFACE_VERSION,
  PLUGIN_MULTI,         // plugin flags
  init,                 // initialize
  nullptr,              // terminate. this pointer can be nullptr
  nullptr,              // invoke the plugin
  nullptr,              // long comment about the plugin
  nullptr,              // multiline help about the plugin
  "Vtil for AMD64",		// the preferred short name of the plugin
  ""					// the preferred hotkey to run the plugin
};