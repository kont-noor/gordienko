class CreateMarkets < ActiveRecord::Migration
  def self.up
    create_table :markets do |t|
      t.string :code
      t.string :name
      t.timestamps
    end
  end

  def self.down
    drop_table :markets
  end
end
