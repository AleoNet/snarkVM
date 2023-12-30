program mappings.aleo;

mapping m_u64:
    key as u64.public;
    value as u64.public;

mapping m_field:
    key as u64.public;
    value as field.public;

mapping m_group:
    key as u64.public;
    value as group.public;

mapping m_field_array_depth_0_length_2:
    key as u64.public;
    value as [field; 2u32].public;

mapping m_field_array_depth_0_length_4:
    key as u64.public;
    value as [field; 4u32].public;

mapping m_field_array_depth_0_length_8:
    key as u64.public;
    value as [field; 8u32].public;

mapping m_field_array_depth_0_length_16:
    key as u64.public;
    value as [field; 16u32].public;

mapping m_field_array_depth_1_length_2:
    key as u64.public;
    value as [[field; 2u32]; 2u32].public;

mapping m_field_array_depth_1_length_4:
    key as u64.public;
    value as [[field; 4u32]; 4u32].public;

mapping m_field_array_depth_1_length_8:
    key as u64.public;
    value as [[field; 8u32]; 8u32].public;

mapping m_field_array_depth_1_length_16:
    key as u64.public;
    value as [[field; 16u32]; 16u32].public;

mapping m_field_array_depth_2_length_2:
    key as u64.public;
    value as [[[field; 2u32]; 2u32]; 2u32].public;

mapping m_field_array_depth_2_length_4:
    key as u64.public;
    value as [[[field; 4u32]; 4u32]; 4u32].public;

mapping m_field_array_depth_2_length_8:
    key as u64.public;
    value as [[[field; 8u32]; 8u32]; 8u32].public;

function main:
    input r0 as u64.public;
    output r0 as u64.public;

