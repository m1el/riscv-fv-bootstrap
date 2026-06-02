// Lean compiler output
// Module: Hex0.Spec
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_c__nl;
LEAN_EXPORT lean_object* lp_hex0_Hex0_c__sp;
LEAN_EXPORT lean_object* lp_hex0_Hex0_c__us;
LEAN_EXPORT lean_object* lp_hex0_Hex0_c__hash;
LEAN_EXPORT lean_object* lp_hex0_Hex0_c__semi;
LEAN_EXPORT uint8_t lp_hex0_Hex0_isSpace(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_isSpace___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_hex0_Hex0_isComment(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_isComment___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_hex0_Hex0_isLowStop(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_isLowStop___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_nibble(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_nibble___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_hex0_Hex0_Status_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_hex0_Hex0_instDecidableEqStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_hex0_Hex0_instDecidableEqStatus___boxed(lean_object*, lean_object*);
static const lean_string_object lp_hex0_Hex0_instReprStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Hex0.Status.Ok"};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__0 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__0_value;
static const lean_ctor_object lp_hex0_Hex0_instReprStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__0_value)}};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__1 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__1_value;
static const lean_string_object lp_hex0_Hex0_instReprStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Hex0.Status.Split"};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__2 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__2_value;
static const lean_ctor_object lp_hex0_Hex0_instReprStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__2_value)}};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__3 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__3_value;
static const lean_string_object lp_hex0_Hex0_instReprStatus_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Hex0.Status.Trailing"};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__4 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__4_value;
static const lean_ctor_object lp_hex0_Hex0_instReprStatus_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__4_value)}};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__5 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__5_value;
static const lean_string_object lp_hex0_Hex0_instReprStatus_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Hex0.Status.Unknown"};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__6 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__6_value;
static const lean_ctor_object lp_hex0_Hex0_instReprStatus_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__6_value)}};
static const lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__7 = (const lean_object*)&lp_hex0_Hex0_instReprStatus_repr___closed__7_value;
static lean_once_cell_t lp_hex0_Hex0_instReprStatus_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__8;
static lean_once_cell_t lp_hex0_Hex0_instReprStatus_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hex0_Hex0_instReprStatus_repr___closed__9;
LEAN_EXPORT lean_object* lp_hex0_Hex0_instReprStatus_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_instReprStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_hex0_Hex0_instReprStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_hex0_Hex0_instReprStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_hex0_Hex0_instReprStatus___closed__0 = (const lean_object*)&lp_hex0_Hex0_instReprStatus___closed__0_value;
LEAN_EXPORT const lean_object* lp_hex0_Hex0_instReprStatus = (const lean_object*)&lp_hex0_Hex0_instReprStatus___closed__0_value;
LEAN_EXPORT lean_object* lp_hex0_Hex0_skipComment(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_skipComment___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_skipComment_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_skipComment_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_High_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_High_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_Low_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_Low_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_hex0_Hex0_decodeS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* lp_hex0_Hex0_decodeS___closed__0 = (const lean_object*)&lp_hex0_Hex0_decodeS___closed__0_value;
static const lean_ctor_object lp_hex0_Hex0_decodeS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_hex0_Hex0_decodeS___closed__1 = (const lean_object*)&lp_hex0_Hex0_decodeS___closed__1_value;
LEAN_EXPORT lean_object* lp_hex0_Hex0_decodeS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_decode(lean_object*);
LEAN_EXPORT lean_object* lp_hex0_Hex0_statusCode(uint8_t);
LEAN_EXPORT lean_object* lp_hex0_Hex0_statusCode___boxed(lean_object*);
static const lean_array_object lp_hex0_Hex0_coreSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_hex0_Hex0_coreSpec___closed__0 = (const lean_object*)&lp_hex0_Hex0_coreSpec___closed__0_value;
LEAN_EXPORT lean_object* lp_hex0_Hex0_coreSpec(lean_object*, lean_object*);
static lean_object* _init_lp_hex0_Hex0_c__nl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(10u);
return v___x_1_;
}
}
static lean_object* _init_lp_hex0_Hex0_c__sp(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(32u);
return v___x_2_;
}
}
static lean_object* _init_lp_hex0_Hex0_c__us(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(95u);
return v___x_3_;
}
}
static lean_object* _init_lp_hex0_Hex0_c__hash(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(35u);
return v___x_4_;
}
}
static lean_object* _init_lp_hex0_Hex0_c__semi(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(59u);
return v___x_5_;
}
}
LEAN_EXPORT uint8_t lp_hex0_Hex0_isSpace(lean_object* v_c_6_){
_start:
{
uint8_t v___y_8_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(10u);
v___x_12_ = lean_nat_dec_eq(v_c_6_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(32u);
v___x_14_ = lean_nat_dec_eq(v_c_6_, v___x_13_);
v___y_8_ = v___x_14_;
goto v___jp_7_;
}
else
{
v___y_8_ = v___x_12_;
goto v___jp_7_;
}
v___jp_7_:
{
if (v___y_8_ == 0)
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(95u);
v___x_10_ = lean_nat_dec_eq(v_c_6_, v___x_9_);
return v___x_10_;
}
else
{
return v___y_8_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_isSpace___boxed(lean_object* v_c_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = lp_hex0_Hex0_isSpace(v_c_15_);
lean_dec(v_c_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t lp_hex0_Hex0_isComment(lean_object* v_c_18_){
_start:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_unsigned_to_nat(35u);
v___x_20_ = lean_nat_dec_eq(v_c_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(59u);
v___x_22_ = lean_nat_dec_eq(v_c_18_, v___x_21_);
return v___x_22_;
}
else
{
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_isComment___boxed(lean_object* v_c_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lp_hex0_Hex0_isComment(v_c_23_);
lean_dec(v_c_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t lp_hex0_Hex0_isLowStop(lean_object* v_c_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lp_hex0_Hex0_isSpace(v_c_26_);
if (v___x_27_ == 0)
{
uint8_t v___x_28_; 
v___x_28_ = lp_hex0_Hex0_isComment(v_c_26_);
return v___x_28_;
}
else
{
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_isLowStop___boxed(lean_object* v_c_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lp_hex0_Hex0_isLowStop(v_c_29_);
lean_dec(v_c_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_nibble(lean_object* v_c_32_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(48u);
v___x_44_ = lean_nat_dec_le(v___x_43_, v_c_32_);
if (v___x_44_ == 0)
{
goto v___jp_33_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(57u);
v___x_46_ = lean_nat_dec_le(v_c_32_, v___x_45_);
if (v___x_46_ == 0)
{
goto v___jp_33_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_nat_sub(v_c_32_, v___x_43_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
v___jp_33_:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(65u);
v___x_35_ = lean_nat_dec_le(v___x_34_, v_c_32_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(70u);
v___x_38_ = lean_nat_dec_le(v_c_32_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(55u);
v___x_41_ = lean_nat_sub(v_c_32_, v___x_40_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_nibble___boxed(lean_object* v_c_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_hex0_Hex0_nibble(v_c_49_);
lean_dec(v_c_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorIdx(uint8_t v_x_51_){
_start:
{
switch(v_x_51_)
{
case 0:
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(0u);
return v___x_52_;
}
case 1:
{
lean_object* v___x_53_; 
v___x_53_ = lean_unsigned_to_nat(1u);
return v___x_53_;
}
case 2:
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(2u);
return v___x_54_;
}
default: 
{
lean_object* v___x_55_; 
v___x_55_ = lean_unsigned_to_nat(3u);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorIdx___boxed(lean_object* v_x_56_){
_start:
{
uint8_t v_x_boxed_57_; lean_object* v_res_58_; 
v_x_boxed_57_ = lean_unbox(v_x_56_);
v_res_58_ = lp_hex0_Hex0_Status_ctorIdx(v_x_boxed_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_toCtorIdx(uint8_t v_x_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_hex0_Hex0_Status_ctorIdx(v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_toCtorIdx___boxed(lean_object* v_x_61_){
_start:
{
uint8_t v_x_4__boxed_62_; lean_object* v_res_63_; 
v_x_4__boxed_62_ = lean_unbox(v_x_61_);
v_res_63_ = lp_hex0_Hex0_Status_toCtorIdx(v_x_4__boxed_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___redArg(lean_object* v_k_64_){
_start:
{
lean_inc(v_k_64_);
return v_k_64_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___redArg___boxed(lean_object* v_k_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_hex0_Hex0_Status_ctorElim___redArg(v_k_65_);
lean_dec(v_k_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim(lean_object* v_motive_67_, lean_object* v_ctorIdx_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_k_71_){
_start:
{
lean_inc(v_k_71_);
return v_k_71_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ctorElim___boxed(lean_object* v_motive_72_, lean_object* v_ctorIdx_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_k_76_){
_start:
{
uint8_t v_t_boxed_77_; lean_object* v_res_78_; 
v_t_boxed_77_ = lean_unbox(v_t_74_);
v_res_78_ = lp_hex0_Hex0_Status_ctorElim(v_motive_72_, v_ctorIdx_73_, v_t_boxed_77_, v_h_75_, v_k_76_);
lean_dec(v_k_76_);
lean_dec(v_ctorIdx_73_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___redArg(lean_object* v_Ok_79_){
_start:
{
lean_inc(v_Ok_79_);
return v_Ok_79_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___redArg___boxed(lean_object* v_Ok_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_hex0_Hex0_Status_Ok_elim___redArg(v_Ok_80_);
lean_dec(v_Ok_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim(lean_object* v_motive_82_, uint8_t v_t_83_, lean_object* v_h_84_, lean_object* v_Ok_85_){
_start:
{
lean_inc(v_Ok_85_);
return v_Ok_85_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Ok_elim___boxed(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_Ok_89_){
_start:
{
uint8_t v_t_boxed_90_; lean_object* v_res_91_; 
v_t_boxed_90_ = lean_unbox(v_t_87_);
v_res_91_ = lp_hex0_Hex0_Status_Ok_elim(v_motive_86_, v_t_boxed_90_, v_h_88_, v_Ok_89_);
lean_dec(v_Ok_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___redArg(lean_object* v_Split_92_){
_start:
{
lean_inc(v_Split_92_);
return v_Split_92_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___redArg___boxed(lean_object* v_Split_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_hex0_Hex0_Status_Split_elim___redArg(v_Split_93_);
lean_dec(v_Split_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim(lean_object* v_motive_95_, uint8_t v_t_96_, lean_object* v_h_97_, lean_object* v_Split_98_){
_start:
{
lean_inc(v_Split_98_);
return v_Split_98_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Split_elim___boxed(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_Split_102_){
_start:
{
uint8_t v_t_boxed_103_; lean_object* v_res_104_; 
v_t_boxed_103_ = lean_unbox(v_t_100_);
v_res_104_ = lp_hex0_Hex0_Status_Split_elim(v_motive_99_, v_t_boxed_103_, v_h_101_, v_Split_102_);
lean_dec(v_Split_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___redArg(lean_object* v_Trailing_105_){
_start:
{
lean_inc(v_Trailing_105_);
return v_Trailing_105_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___redArg___boxed(lean_object* v_Trailing_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_hex0_Hex0_Status_Trailing_elim___redArg(v_Trailing_106_);
lean_dec(v_Trailing_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim(lean_object* v_motive_108_, uint8_t v_t_109_, lean_object* v_h_110_, lean_object* v_Trailing_111_){
_start:
{
lean_inc(v_Trailing_111_);
return v_Trailing_111_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Trailing_elim___boxed(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_Trailing_115_){
_start:
{
uint8_t v_t_boxed_116_; lean_object* v_res_117_; 
v_t_boxed_116_ = lean_unbox(v_t_113_);
v_res_117_ = lp_hex0_Hex0_Status_Trailing_elim(v_motive_112_, v_t_boxed_116_, v_h_114_, v_Trailing_115_);
lean_dec(v_Trailing_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___redArg(lean_object* v_Unknown_118_){
_start:
{
lean_inc(v_Unknown_118_);
return v_Unknown_118_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___redArg___boxed(lean_object* v_Unknown_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_hex0_Hex0_Status_Unknown_elim___redArg(v_Unknown_119_);
lean_dec(v_Unknown_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim(lean_object* v_motive_121_, uint8_t v_t_122_, lean_object* v_h_123_, lean_object* v_Unknown_124_){
_start:
{
lean_inc(v_Unknown_124_);
return v_Unknown_124_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_Unknown_elim___boxed(lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_Unknown_128_){
_start:
{
uint8_t v_t_boxed_129_; lean_object* v_res_130_; 
v_t_boxed_129_ = lean_unbox(v_t_126_);
v_res_130_ = lp_hex0_Hex0_Status_Unknown_elim(v_motive_125_, v_t_boxed_129_, v_h_127_, v_Unknown_128_);
lean_dec(v_Unknown_128_);
return v_res_130_;
}
}
LEAN_EXPORT uint8_t lp_hex0_Hex0_Status_ofNat(lean_object* v_n_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_dec_le(v_n_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(2u);
v___x_135_ = lean_nat_dec_le(v_n_131_, v___x_134_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
v___x_136_ = 3;
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 2;
return v___x_137_;
}
}
else
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_nat_dec_le(v_n_131_, v___x_138_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_Status_ofNat___boxed(lean_object* v_n_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = lp_hex0_Hex0_Status_ofNat(v_n_142_);
lean_dec(v_n_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t lp_hex0_Hex0_instDecidableEqStatus(uint8_t v_x_145_, uint8_t v_y_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lp_hex0_Hex0_Status_ctorIdx(v_x_145_);
v___x_148_ = lp_hex0_Hex0_Status_ctorIdx(v_y_146_);
v___x_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
lean_dec(v___x_148_);
lean_dec(v___x_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_instDecidableEqStatus___boxed(lean_object* v_x_150_, lean_object* v_y_151_){
_start:
{
uint8_t v_x_13__boxed_152_; uint8_t v_y_14__boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_x_13__boxed_152_ = lean_unbox(v_x_150_);
v_y_14__boxed_153_ = lean_unbox(v_y_151_);
v_res_154_ = lp_hex0_Hex0_instDecidableEqStatus(v_x_13__boxed_152_, v_y_14__boxed_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static lean_object* _init_lp_hex0_Hex0_instReprStatus_repr___closed__8(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(2u);
v___x_169_ = lean_nat_to_int(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_lp_hex0_Hex0_instReprStatus_repr___closed__9(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_to_int(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_instReprStatus_repr(uint8_t v_x_172_, lean_object* v_prec_173_){
_start:
{
lean_object* v___y_175_; lean_object* v___y_182_; lean_object* v___y_189_; lean_object* v___y_196_; 
switch(v_x_172_)
{
case 0:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(1024u);
v___x_203_ = lean_nat_dec_le(v___x_202_, v_prec_173_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__8, &lp_hex0_Hex0_instReprStatus_repr___closed__8_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__8);
v___y_175_ = v___x_204_;
goto v___jp_174_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__9, &lp_hex0_Hex0_instReprStatus_repr___closed__9_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__9);
v___y_175_ = v___x_205_;
goto v___jp_174_;
}
}
case 1:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1024u);
v___x_207_ = lean_nat_dec_le(v___x_206_, v_prec_173_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__8, &lp_hex0_Hex0_instReprStatus_repr___closed__8_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__8);
v___y_182_ = v___x_208_;
goto v___jp_181_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__9, &lp_hex0_Hex0_instReprStatus_repr___closed__9_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__9);
v___y_182_ = v___x_209_;
goto v___jp_181_;
}
}
case 2:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1024u);
v___x_211_ = lean_nat_dec_le(v___x_210_, v_prec_173_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__8, &lp_hex0_Hex0_instReprStatus_repr___closed__8_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__8);
v___y_189_ = v___x_212_;
goto v___jp_188_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__9, &lp_hex0_Hex0_instReprStatus_repr___closed__9_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__9);
v___y_189_ = v___x_213_;
goto v___jp_188_;
}
}
default: 
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1024u);
v___x_215_ = lean_nat_dec_le(v___x_214_, v_prec_173_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__8, &lp_hex0_Hex0_instReprStatus_repr___closed__8_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__8);
v___y_196_ = v___x_216_;
goto v___jp_195_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&lp_hex0_Hex0_instReprStatus_repr___closed__9, &lp_hex0_Hex0_instReprStatus_repr___closed__9_once, _init_lp_hex0_Hex0_instReprStatus_repr___closed__9);
v___y_196_ = v___x_217_;
goto v___jp_195_;
}
}
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = ((lean_object*)(lp_hex0_Hex0_instReprStatus_repr___closed__1));
lean_inc(v___y_175_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = l_Repr_addAppParen(v___x_179_, v_prec_173_);
return v___x_180_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = ((lean_object*)(lp_hex0_Hex0_instReprStatus_repr___closed__3));
lean_inc(v___y_182_);
v___x_184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_184_, 0, v___y_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = l_Repr_addAppParen(v___x_186_, v_prec_173_);
return v___x_187_;
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = ((lean_object*)(lp_hex0_Hex0_instReprStatus_repr___closed__5));
lean_inc(v___y_189_);
v___x_191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_191_, 0, v___y_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = 0;
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_192_);
v___x_194_ = l_Repr_addAppParen(v___x_193_, v_prec_173_);
return v___x_194_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = ((lean_object*)(lp_hex0_Hex0_instReprStatus_repr___closed__7));
lean_inc(v___y_196_);
v___x_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_198_, 0, v___y_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = 0;
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_199_);
v___x_201_ = l_Repr_addAppParen(v___x_200_, v_prec_173_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_instReprStatus_repr___boxed(lean_object* v_x_218_, lean_object* v_prec_219_){
_start:
{
uint8_t v_x_233__boxed_220_; lean_object* v_res_221_; 
v_x_233__boxed_220_ = lean_unbox(v_x_218_);
v_res_221_ = lp_hex0_Hex0_instReprStatus_repr(v_x_233__boxed_220_, v_prec_219_);
lean_dec(v_prec_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_skipComment(lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
return v_x_224_;
}
else
{
lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_head_225_ = lean_ctor_get(v_x_224_, 0);
v_tail_226_ = lean_ctor_get(v_x_224_, 1);
v___x_227_ = lean_unsigned_to_nat(10u);
v___x_228_ = lean_nat_dec_eq(v_head_225_, v___x_227_);
if (v___x_228_ == 0)
{
v_x_224_ = v_tail_226_;
goto _start;
}
else
{
lean_inc(v_tail_226_);
return v_tail_226_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_skipComment___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = lp_hex0_Hex0_skipComment(v_x_230_);
lean_dec(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_skipComment_match__1_splitter___redArg(lean_object* v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_h__2_234_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_apply_1(v_h__1_233_, v___x_235_);
return v___x_236_;
}
else
{
lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v___x_239_; 
lean_dec(v_h__1_233_);
v_head_237_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_head_237_);
v_tail_238_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_tail_238_);
lean_dec_ref(v_x_232_);
v___x_239_ = lean_apply_2(v_h__2_234_, v_head_237_, v_tail_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_skipComment_match__1_splitter(lean_object* v_motive_240_, lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__2_243_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__1_242_, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v_head_246_; lean_object* v_tail_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_242_);
v_head_246_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_head_246_);
v_tail_247_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_tail_247_);
lean_dec_ref(v_x_241_);
v___x_248_ = lean_apply_2(v_h__2_243_, v_head_246_, v_tail_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorIdx(lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(0u);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(1u);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorIdx___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = lp_hex0_Hex0_St_ctorIdx(v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim___redArg(lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
if (lean_obj_tag(v_t_254_) == 0)
{
return v_k_255_;
}
else
{
lean_object* v_hi_256_; lean_object* v___x_257_; 
v_hi_256_ = lean_ctor_get(v_t_254_, 0);
lean_inc(v_hi_256_);
lean_dec_ref(v_t_254_);
v___x_257_ = lean_apply_1(v_k_255_, v_hi_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim(lean_object* v_motive_258_, lean_object* v_ctorIdx_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_k_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lp_hex0_Hex0_St_ctorElim___redArg(v_t_260_, v_k_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_ctorElim___boxed(lean_object* v_motive_264_, lean_object* v_ctorIdx_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_k_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_hex0_Hex0_St_ctorElim(v_motive_264_, v_ctorIdx_265_, v_t_266_, v_h_267_, v_k_268_);
lean_dec(v_ctorIdx_265_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_High_elim___redArg(lean_object* v_t_270_, lean_object* v_High_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lp_hex0_Hex0_St_ctorElim___redArg(v_t_270_, v_High_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_High_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_High_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lp_hex0_Hex0_St_ctorElim___redArg(v_t_274_, v_High_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_Low_elim___redArg(lean_object* v_t_278_, lean_object* v_Low_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lp_hex0_Hex0_St_ctorElim___redArg(v_t_278_, v_Low_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_St_Low_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_Low_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lp_hex0_Hex0_St_ctorElim___redArg(v_t_282_, v_Low_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_decodeS(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
if (lean_obj_tag(v_x_295_) == 0)
{
uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = 0;
v___x_297_ = lean_box(v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_x_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; uint8_t v___x_301_; 
v_head_299_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_head_299_);
v_tail_300_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_tail_300_);
lean_dec_ref(v_x_295_);
v___x_301_ = lp_hex0_Hex0_isComment(v_head_299_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = lp_hex0_Hex0_isSpace(v_head_299_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lp_hex0_Hex0_nibble(v_head_299_);
lean_dec(v_head_299_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_304_; 
lean_dec(v_tail_300_);
v___x_304_ = ((lean_object*)(lp_hex0_Hex0_decodeS___closed__0));
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_val_305_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_val_305_);
v___x_310_ = v_reuseFailAlloc_312_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
v_x_294_ = v___x_310_;
v_x_295_ = v_tail_300_;
goto _start;
}
}
}
}
else
{
lean_dec(v_head_299_);
v_x_295_ = v_tail_300_;
goto _start;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_head_299_);
v___x_315_ = lp_hex0_Hex0_skipComment(v_tail_300_);
lean_dec(v_tail_300_);
v_x_295_ = v___x_315_;
goto _start;
}
}
}
else
{
if (lean_obj_tag(v_x_295_) == 0)
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref(v_x_294_);
v___x_317_ = 2;
v___x_318_ = lean_box(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_x_295_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
else
{
lean_object* v_hi_320_; lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_348_; 
v_hi_320_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_hi_320_);
lean_dec_ref(v_x_294_);
v_head_321_ = lean_ctor_get(v_x_295_, 0);
v_tail_322_ = lean_ctor_get(v_x_295_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_348_ == 0)
{
v___x_324_ = v_x_295_;
v_isShared_325_ = v_isSharedCheck_348_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_head_321_);
lean_dec(v_x_295_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_348_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = lp_hex0_Hex0_isLowStop(v_head_321_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lp_hex0_Hex0_nibble(v_head_321_);
lean_dec(v_head_321_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; 
lean_del_object(v___x_324_);
lean_dec(v_tail_322_);
lean_dec(v_hi_320_);
v___x_328_ = ((lean_object*)(lp_hex0_Hex0_decodeS___closed__0));
return v___x_328_;
}
else
{
lean_object* v_val_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_346_; 
v_val_329_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_329_);
lean_dec_ref(v___x_327_);
v___x_330_ = lean_box(0);
v___x_331_ = lp_hex0_Hex0_decodeS(v___x_330_, v_tail_322_);
v_fst_332_ = lean_ctor_get(v___x_331_, 0);
v_snd_333_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_346_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snd_333_);
lean_inc(v_fst_332_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_337_ = lean_unsigned_to_nat(16u);
v___x_338_ = lean_nat_mul(v_hi_320_, v___x_337_);
lean_dec(v_hi_320_);
v___x_339_ = lean_nat_add(v___x_338_, v_val_329_);
lean_dec(v_val_329_);
lean_dec(v___x_338_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_fst_332_);
lean_ctor_set(v___x_324_, 0, v___x_339_);
v___x_341_ = v___x_324_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_fst_332_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_341_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_snd_333_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
lean_object* v___x_347_; 
lean_del_object(v___x_324_);
lean_dec(v_tail_322_);
lean_dec(v_head_321_);
lean_dec(v_hi_320_);
v___x_347_ = ((lean_object*)(lp_hex0_Hex0_decodeS___closed__1));
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__5_splitter___redArg(lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_, lean_object* v_h__3_353_, lean_object* v_h__4_354_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_dec(v_h__4_354_);
lean_dec(v_h__2_352_);
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_h__3_353_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_apply_1(v_h__1_351_, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v_head_357_; lean_object* v_tail_358_; lean_object* v___x_359_; 
lean_dec(v_h__1_351_);
v_head_357_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_head_357_);
v_tail_358_ = lean_ctor_get(v_x_350_, 1);
lean_inc(v_tail_358_);
lean_dec_ref(v_x_350_);
v___x_359_ = lean_apply_2(v_h__3_353_, v_head_357_, v_tail_358_);
return v___x_359_;
}
}
else
{
lean_dec(v_h__3_353_);
lean_dec(v_h__1_351_);
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_hi_360_; lean_object* v___x_361_; 
lean_dec(v_h__4_354_);
v_hi_360_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_hi_360_);
lean_dec_ref(v_x_349_);
v___x_361_ = lean_apply_1(v_h__2_352_, v_hi_360_);
return v___x_361_;
}
else
{
lean_object* v_hi_362_; lean_object* v_head_363_; lean_object* v_tail_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_352_);
v_hi_362_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_hi_362_);
lean_dec_ref(v_x_349_);
v_head_363_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_head_363_);
v_tail_364_ = lean_ctor_get(v_x_350_, 1);
lean_inc(v_tail_364_);
lean_dec_ref(v_x_350_);
v___x_365_ = lean_apply_3(v_h__4_354_, v_hi_362_, v_head_363_, v_tail_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__5_splitter(lean_object* v_motive_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_, lean_object* v_h__3_371_, lean_object* v_h__4_372_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_dec(v_h__4_372_);
lean_dec(v_h__2_370_);
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_h__3_371_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_apply_1(v_h__1_369_, v___x_373_);
return v___x_374_;
}
else
{
lean_object* v_head_375_; lean_object* v_tail_376_; lean_object* v___x_377_; 
lean_dec(v_h__1_369_);
v_head_375_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_head_375_);
v_tail_376_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_tail_376_);
lean_dec_ref(v_x_368_);
v___x_377_ = lean_apply_2(v_h__3_371_, v_head_375_, v_tail_376_);
return v___x_377_;
}
}
else
{
lean_dec(v_h__3_371_);
lean_dec(v_h__1_369_);
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_hi_378_; lean_object* v___x_379_; 
lean_dec(v_h__4_372_);
v_hi_378_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_hi_378_);
lean_dec_ref(v_x_367_);
v___x_379_ = lean_apply_1(v_h__2_370_, v_hi_378_);
return v___x_379_;
}
else
{
lean_object* v_hi_380_; lean_object* v_head_381_; lean_object* v_tail_382_; lean_object* v___x_383_; 
lean_dec(v_h__2_370_);
v_hi_380_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_hi_380_);
lean_dec_ref(v_x_367_);
v_head_381_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_head_381_);
v_tail_382_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_tail_382_);
lean_dec_ref(v_x_368_);
v___x_383_ = lean_apply_3(v_h__4_372_, v_hi_380_, v_head_381_, v_tail_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__1_splitter___redArg(lean_object* v_x_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_h__2_386_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_apply_1(v_h__1_385_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v_val_389_; lean_object* v___x_390_; 
lean_dec(v_h__1_385_);
v_val_389_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_val_389_);
lean_dec_ref(v_x_384_);
v___x_390_ = lean_apply_1(v_h__2_386_, v_val_389_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__1_splitter(lean_object* v_motive_391_, lean_object* v_x_392_, lean_object* v_h__1_393_, lean_object* v_h__2_394_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_394_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_apply_1(v_h__1_393_, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v_val_397_; lean_object* v___x_398_; 
lean_dec(v_h__1_393_);
v_val_397_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_x_392_);
v___x_398_ = lean_apply_1(v_h__2_394_, v_val_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__3_splitter___redArg(lean_object* v_x_399_, lean_object* v_h__1_400_){
_start:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_403_; 
v_fst_401_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v_x_399_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v_x_399_);
v___x_403_ = lean_apply_2(v_h__1_400_, v_fst_401_, v_snd_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* lp_hex0___private_Hex0_Spec_0__Hex0_decodeS_match__3_splitter(lean_object* v_motive_404_, lean_object* v_x_405_, lean_object* v_h__1_406_){
_start:
{
lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_409_; 
v_fst_407_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_snd_408_);
lean_dec_ref(v_x_405_);
v___x_409_ = lean_apply_2(v_h__1_406_, v_fst_407_, v_snd_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_decode(lean_object* v_l_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_box(0);
v___x_412_ = lp_hex0_Hex0_decodeS(v___x_411_, v_l_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_statusCode(uint8_t v_x_413_){
_start:
{
switch(v_x_413_)
{
case 0:
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(0u);
return v___x_414_;
}
case 1:
{
lean_object* v___x_415_; 
v___x_415_ = lean_unsigned_to_nat(3u);
return v___x_415_;
}
case 2:
{
lean_object* v___x_416_; 
v___x_416_ = lean_unsigned_to_nat(4u);
return v___x_416_;
}
default: 
{
lean_object* v___x_417_; 
v___x_417_ = lean_unsigned_to_nat(5u);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_statusCode___boxed(lean_object* v_x_418_){
_start:
{
uint8_t v_x_44__boxed_419_; lean_object* v_res_420_; 
v_x_44__boxed_419_ = lean_unbox(v_x_418_);
v_res_420_ = lp_hex0_Hex0_statusCode(v_x_44__boxed_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* lp_hex0_Hex0_coreSpec(lean_object* v_input_423_, lean_object* v_cap_424_){
_start:
{
lean_object* v___x_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_446_; 
v___x_425_ = lp_hex0_Hex0_decode(v_input_423_);
v_fst_426_ = lean_ctor_get(v___x_425_, 0);
v_snd_427_ = lean_ctor_get(v___x_425_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_446_ == 0)
{
v___x_429_ = v___x_425_;
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v___x_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = l_List_lengthTR___redArg(v_fst_426_);
v___x_432_ = lean_nat_dec_lt(v_cap_424_, v___x_431_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec(v_cap_424_);
v___x_433_ = lean_unbox(v_snd_427_);
lean_dec(v_snd_427_);
v___x_434_ = lp_hex0_Hex0_statusCode(v___x_433_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_431_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_431_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
return v___x_437_;
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec(v___x_431_);
lean_dec(v_snd_427_);
v___x_439_ = lean_unsigned_to_nat(2u);
v___x_440_ = ((lean_object*)(lp_hex0_Hex0_coreSpec___closed__0));
lean_inc(v_cap_424_);
lean_inc(v_fst_426_);
v___x_441_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_fst_426_, v_fst_426_, v_cap_424_, v___x_440_);
lean_dec(v_fst_426_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_cap_424_);
lean_ctor_set(v___x_429_, 0, v___x_441_);
v___x_443_ = v___x_429_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_cap_424_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_439_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
return v___x_444_;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_hex0_Hex0_Spec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_hex0_Hex0_c__nl = _init_lp_hex0_Hex0_c__nl();
lean_mark_persistent(lp_hex0_Hex0_c__nl);
lp_hex0_Hex0_c__sp = _init_lp_hex0_Hex0_c__sp();
lean_mark_persistent(lp_hex0_Hex0_c__sp);
lp_hex0_Hex0_c__us = _init_lp_hex0_Hex0_c__us();
lean_mark_persistent(lp_hex0_Hex0_c__us);
lp_hex0_Hex0_c__hash = _init_lp_hex0_Hex0_c__hash();
lean_mark_persistent(lp_hex0_Hex0_c__hash);
lp_hex0_Hex0_c__semi = _init_lp_hex0_Hex0_c__semi();
lean_mark_persistent(lp_hex0_Hex0_c__semi);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
